import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

/* ============================================================
   종이 접기 3D — 평면 접기(flat fold) + 오리기 + 옮기기
   종이 = 볼록 다각형 조각(facet)들의 목록.
   facet = { pts: 종이좌표 다각형(CCW), T: 종이→테이블 2D 등거리변환, layer: 정수, pieceId: 조각 번호 }
   접기 = "잡은 점 P를 놓은 점 Q로" — 접는 선은 PQ의 수직이등분선 (P가 속한 조각만 접힘)
   오리기 = 직선으로 전 조각 클리핑, 양쪽에 다른 pieceId 부여
   ============================================================ */

const LAYER_EPS = 0.1;        // 층 간격 (종이 두께)
const MIN_AREA = 0.02;        // 이 미만 조각은 버림
const BASE_H = 29.7;          // 종이 높이 고정(A4), 폭은 이미지 비율 따름
const FOLD_ANIM_MS = 150;     // 놓은 뒤 정착 애니메이션 시간

let paperW = 21.0;
let paperH = BASE_H;

// ---------- 2D 기하 유틸 ----------
const applyT = (T, p) => ({ x: T.a * p.x + T.b * p.y + T.tx, y: T.c * p.x + T.d * p.y + T.ty });

function reflectAcross(L0, u) { // 테이블 공간에서 직선(L0, 방향 u) 반사 행렬
  const m00 = 2 * u.x * u.x - 1, m01 = 2 * u.x * u.y;
  const m10 = m01, m11 = 2 * u.y * u.y - 1;
  return {
    m00, m01, m10, m11,
    tx: L0.x - (m00 * L0.x + m01 * L0.y),
    ty: L0.y - (m10 * L0.x + m11 * L0.y),
  };
}
function rotationAround(c, ang) { // 점 c 중심 회전 행렬
  const co = Math.cos(ang), si = Math.sin(ang);
  return {
    m00: co, m01: -si, m10: si, m11: co,
    tx: c.x - (co * c.x - si * c.y),
    ty: c.y - (si * c.x + co * c.y),
  };
}
function composeRT(R, T) { // (행렬 R) ∘ (변환 T)
  return {
    a: R.m00 * T.a + R.m01 * T.c,
    b: R.m00 * T.b + R.m01 * T.d,
    c: R.m10 * T.a + R.m11 * T.c,
    d: R.m10 * T.b + R.m11 * T.d,
    tx: R.m00 * T.tx + R.m01 * T.ty + R.tx,
    ty: R.m10 * T.tx + R.m11 * T.ty + R.ty,
  };
}
const translateT = (T, dx, dy) => ({ ...T, tx: T.tx + dx, ty: T.ty + dy });
function invertT(T) {
  const det = T.a * T.d - T.b * T.c;
  const a = T.d / det, b = -T.b / det, c = -T.c / det, d = T.a / det;
  return { a, b, c, d, tx: -(a * T.tx + b * T.ty), ty: -(c * T.tx + d * T.ty) };
}

function polyArea(pts) {
  let s = 0;
  for (let i = 0; i < pts.length; i++) {
    const a = pts[i], b = pts[(i + 1) % pts.length];
    s += a.x * b.y - b.x * a.y;
  }
  return Math.abs(s) / 2;
}
// Sutherland-Hodgman: gvals[i] 부호 기준으로 반평면 클리핑
function clipPoly(pts, gvals, keepPositive) {
  const out = [];
  const n = pts.length;
  for (let i = 0; i < n; i++) {
    const a = pts[i], b = pts[(i + 1) % n];
    const ga = gvals[i], gb = gvals[(i + 1) % n];
    const ain = keepPositive ? ga >= -1e-9 : ga <= 1e-9;
    const bin = keepPositive ? gb >= -1e-9 : gb <= 1e-9;
    if (ain) out.push(a);
    if (ain !== bin) {
      const t = ga / (ga - gb);
      out.push({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });
    }
  }
  return out;
}
function signedArea(pts) {
  let s = 0;
  for (let i = 0; i < pts.length; i++) {
    const a = pts[i], b = pts[(i + 1) % pts.length];
    s += a.x * b.y - b.x * a.y;
  }
  return s / 2;
}
function polysOverlap(A, B) { // 볼록끼리 겹침 (테두리만 닿는 건 제외)
  let clip = signedArea(B) < 0 ? [...B].reverse() : B;
  let cur = A;
  for (let i = 0; i < clip.length && cur.length >= 3; i++) {
    const a = clip[i], b = clip[(i + 1) % clip.length];
    const gv = cur.map(p => (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x));
    cur = clipPoly(cur, gv, true);
  }
  return cur.length >= 3 && polyArea(cur) > 0.08;
}
function pointInConvex(p, pts) { // 볼록 다각형(임의 와인딩) 내부 판정
  let sign = 0;
  for (let i = 0; i < pts.length; i++) {
    const a = pts[i], b = pts[(i + 1) % pts.length];
    const cr = (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x);
    if (Math.abs(cr) < 1e-9) continue;
    const s = Math.sign(cr);
    if (sign === 0) sign = s;
    else if (s !== sign) return false;
  }
  return true;
}

// ---------- 상태 ----------
function initialFacet() {
  return {
    pts: [{ x: 0, y: 0 }, { x: paperW, y: 0 }, { x: paperW, y: paperH }, { x: 0, y: paperH }],
    T: { a: 1, b: 0, c: 0, d: 1, tx: -paperW / 2, ty: -paperH / 2 },
    layer: 0,
    pieceId: 0,
  };
}
let facets = [initialFacet()];
const undoStack = [];
let mode = 'view';           // view | fold | cut | move
let spreadMode = false;      // 키트 펼침 상태 (setMode가 시작 시 먼저 호출되므로 여기서 선언)
let lightMode = false;
let foldDir = 'over';        // over | under
let selectedPiece = null;    // 옮기기 모드에서 마지막으로 잡은 조각

function pushUndo() { undoStack.push(structuredClone(facets)); if (undoStack.length > 60) undoStack.shift(); }
function maxLayer() { return Math.max(...facets.map(f => f.layer)); }
function nextPieceId() { return Math.max(...facets.map(f => f.pieceId)) + 1; }

// 층 정리(중력): 겹치지 않는 조각은 아래로 — 펴진 부분이 공중에 뜨지 않게
function compactLayers() {
  const items = facets
    .map(f => ({ f, poly: f.pts.map(p => applyT(f.T, p)) }))
    .sort((a, b) => a.f.layer - b.f.layer); // 안정 정렬: 기존 상하관계 유지
  const placed = [];
  for (const it of items) {
    let l = 0;
    for (const q of placed) {
      if (polysOverlap(it.poly, q.poly)) l = Math.max(l, q.l + 1);
    }
    it.f.layer = l;
    placed.push({ poly: it.poly, l });
  }
}

// ---------- three.js 셋업 ----------
const canvas = document.getElementById('view');
const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.setSize(window.innerWidth, window.innerHeight);

const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(45, window.innerWidth / window.innerHeight, 0.1, 500);
camera.up.set(0, 0, 1);
camera.position.set(0, -42, 30);

const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.dampingFactor = 0.08;
controls.target.set(0, 0, 0);

// 도구 모드에서는 좌클릭/한 손가락 = 도구, 우클릭/두 손가락 = 회전
function setControlsForTool(toolActive) {
  controls.enabled = true;
  if (toolActive) {
    controls.mouseButtons = { LEFT: null, MIDDLE: THREE.MOUSE.DOLLY, RIGHT: THREE.MOUSE.ROTATE };
    controls.touches = { ONE: null, TWO: THREE.TOUCH.DOLLY_ROTATE };
  } else {
    controls.mouseButtons = { LEFT: THREE.MOUSE.ROTATE, MIDDLE: THREE.MOUSE.DOLLY, RIGHT: THREE.MOUSE.PAN };
    controls.touches = { ONE: THREE.TOUCH.ROTATE, TWO: THREE.TOUCH.DOLLY_PAN };
  }
}

// 카메라 극각(polar) 애니메이션 — THREE.Spherical은 Y축 극이라 Z-up에 맞게 쿼터니언 보정
let flipAnim = null;
const _sph = new THREE.Spherical();
const _upQ = new THREE.Quaternion();
const _upQInv = new THREE.Quaternion();
function getPolar() {
  _upQ.setFromUnitVectors(camera.up, new THREE.Vector3(0, 1, 0));
  _upQInv.copy(_upQ).invert();
  const off = camera.position.clone().sub(controls.target).applyQuaternion(_upQ);
  _sph.setFromVector3(off);
  return _sph;
}
function setPolar(r, phi, theta) {
  const v = new THREE.Vector3().setFromSphericalCoords(r, phi, theta).applyQuaternion(_upQInv);
  camera.position.copy(controls.target).add(v);
}
function animatePolarTo(phiTarget) {
  const s = getPolar();
  flipAnim = { t0: performance.now(), from: s.phi, to: phiTarget, theta: s.theta, r: s.radius };
}
function startFlip() {
  const s = getPolar();
  animatePolarTo(Math.min(Math.PI - 0.03, Math.max(0.03, Math.PI - s.phi)));
}
function alignTopDown() { // 보고 있던 면의 정면으로
  const s = getPolar();
  animatePolarTo(s.phi > Math.PI / 2 ? Math.PI - 0.12 : 0.12);
}

window.addEventListener('resize', () => {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
});

// ---------- 텍스처 ----------
let frontImg = null, backImg = null;
let texFront, texBack, texCombined;

function makeDefaultSide(label, bg) {
  const c = document.createElement('canvas');
  c.width = 724; c.height = 1024;
  const g = c.getContext('2d');
  g.fillStyle = bg; g.fillRect(0, 0, c.width, c.height);
  g.strokeStyle = 'rgba(0,0,0,0.10)'; g.lineWidth = 6;
  g.strokeRect(14, 14, c.width - 28, c.height - 28);
  g.fillStyle = 'rgba(0,0,0,0.07)';
  g.font = 'bold 130px sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle';
  g.fillText(label, c.width / 2, c.height / 2);
  return c;
}

function rebuildTextures() {
  const srcFront = frontImg || makeDefaultSide('앞', '#fdfdf8');
  const srcBack = backImg || makeDefaultSide('뒤', '#f3ecd9');
  const fw = srcFront.width || srcFront.naturalWidth;
  const fh = srcFront.height || srcFront.naturalHeight;
  const scale = Math.min(1, 2048 / Math.max(fw, fh));
  const w = Math.max(64, Math.round(fw * scale));
  const h = Math.max(64, Math.round(fh * scale));

  const cf = document.createElement('canvas'); cf.width = w; cf.height = h;
  cf.getContext('2d').drawImage(srcFront, 0, 0, w, h);

  // 뒷면: 좌우 미러 (실물 종이를 뒤에서 보는 좌표와 일치)
  const cb = document.createElement('canvas'); cb.width = w; cb.height = h;
  const gb = cb.getContext('2d');
  gb.translate(w, 0); gb.scale(-1, 1);
  gb.drawImage(srcBack, 0, 0, w, h);

  // 빛에 비추기: 앞면 × 미러된 뒷면
  const cc = document.createElement('canvas'); cc.width = w; cc.height = h;
  const gc = cc.getContext('2d');
  gc.drawImage(cf, 0, 0);
  gc.globalCompositeOperation = 'multiply';
  gc.drawImage(cb, 0, 0);

  const mk = (cnv) => {
    const t = new THREE.CanvasTexture(cnv);
    t.colorSpace = THREE.SRGBColorSpace;
    t.anisotropy = renderer.capabilities.getMaxAnisotropy();
    return t;
  };
  texFront?.dispose(); texBack?.dispose(); texCombined?.dispose();
  texFront = mk(cf); texBack = mk(cb); texCombined = mk(cc);
  applyMaterialMode();
}

// ---------- 재질 ----------
const matFront = new THREE.MeshBasicMaterial({ side: THREE.FrontSide });
const matBack = new THREE.MeshBasicMaterial({ side: THREE.BackSide });
const matEdge = new THREE.LineBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.18 });
const matFoldLine = new THREE.LineBasicMaterial({ color: 0xff4455 });
const matCreaseLine = new THREE.LineBasicMaterial({ color: 0x33ff88 }); // 기존 접힌 선에 스냅됨 (펴기)
const matCutLine = new THREE.LineBasicMaterial({ color: 0x66d9ff });
const matFoldDash = new THREE.LineDashedMaterial({ color: 0xff4455, dashSize: 0.8, gapSize: 0.5, transparent: true, opacity: 0.6 });
const matCutDash = new THREE.LineDashedMaterial({ color: 0x66d9ff, dashSize: 0.8, gapSize: 0.5, transparent: true, opacity: 0.6 });
const matHighlight = new THREE.MeshBasicMaterial({ color: 0xffa040, transparent: true, opacity: 0.38, side: THREE.DoubleSide, depthTest: false });
const matPieceSel = new THREE.MeshBasicMaterial({ color: 0x4f7cff, transparent: true, opacity: 0.25, side: THREE.DoubleSide, depthTest: false });

function applyMaterialMode() {
  if (lightMode) {
    matFront.map = texCombined; matBack.map = texCombined;
    matFront.transparent = matBack.transparent = true;
    matFront.opacity = matBack.opacity = 0.8;
    matFront.depthWrite = matBack.depthWrite = false;
  } else {
    matFront.map = texFront; matBack.map = texBack;
    matFront.transparent = matBack.transparent = false;
    matFront.opacity = matBack.opacity = 1;
    matFront.depthWrite = matBack.depthWrite = true;
  }
  matFront.needsUpdate = true; matBack.needsUpdate = true;
}

// ---------- 메시 생성 ----------
const paperGroup = new THREE.Group();     // 고정된 facet
const previewGroup = new THREE.Group();   // 접히는 중/옮기는 중 facet (행렬 애니메이션)
const overlayGroup = new THREE.Group();   // 선·하이라이트
previewGroup.matrixAutoUpdate = false;
scene.add(paperGroup, previewGroup, overlayGroup);

function facetGeometry(facet, zOverride = null) {
  const n = facet.pts.length;
  const z = zOverride ?? facet.layer * LAYER_EPS;
  const pos = new Float32Array(n * 3);
  const uv = new Float32Array(n * 2);
  for (let i = 0; i < n; i++) {
    const tp = applyT(facet.T, facet.pts[i]);
    pos[i * 3] = tp.x; pos[i * 3 + 1] = tp.y; pos[i * 3 + 2] = z;
    uv[i * 2] = facet.pts[i].x / paperW; uv[i * 2 + 1] = facet.pts[i].y / paperH;
  }
  const idx = [];
  for (let i = 1; i < n - 1; i++) idx.push(0, i, i + 1);
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(pos, 3));
  geo.setAttribute('uv', new THREE.BufferAttribute(uv, 2));
  geo.setIndex(idx);
  return geo;
}

function buildFacetInto(group, facet) {
  const geo = facetGeometry(facet);
  const m1 = new THREE.Mesh(geo, matFront);
  const m2 = new THREE.Mesh(geo, matBack);
  m1.renderOrder = m2.renderOrder = 1000 + facet.layer;
  group.add(m1, m2);
  // 조각 테두리 — 인덱스 없이 외곽 정점만 연결
  const z = facet.layer * LAYER_EPS + 0.012;
  const edgePts = facet.pts.map(p => {
    const tp = applyT(facet.T, p);
    return new THREE.Vector3(tp.x, tp.y, z);
  });
  const edge = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(edgePts), matEdge);
  edge.renderOrder = 3000;
  group.add(edge);
}

function clearGroup(g) {
  for (const child of [...g.children]) {
    child.geometry?.dispose();
    g.remove(child);
  }
}

// excludeTest: 해당 facet은 previewGroup으로 (애니메이션용)
function rebuildScene(excludeTest = null) {
  clearGroup(paperGroup); clearGroup(previewGroup); clearGroup(overlayGroup);
  previewGroup.matrix.identity();
  for (const f of facets) {
    if (excludeTest && excludeTest(f)) buildFacetInto(previewGroup, f);
    else buildFacetInto(paperGroup, f);
  }
  refreshSnapCache();
}

// ---------- 스냅 ----------
let snapCache = [];
let creaseLines = []; // 접힌 선 후보: 같은 직선 위 에지가 2번 이상 등장 (= 접힌 자리)
function refreshSnapCache() {
  snapCache = [];
  const seen = new Set();
  const lineCount = []; // { A, u, count } — 같은 직선 위 에지 개수
  for (const f of facets) {
    const z = f.layer * LAYER_EPS;
    const tp = f.pts.map(p => applyT(f.T, p));
    for (let i = 0; i < tp.length; i++) {
      const a = tp[i], b = tp[(i + 1) % tp.length];
      for (const c of [a, { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 }]) {
        const key = `${Math.round(c.x * 25)},${Math.round(c.y * 25)}`;
        if (!seen.has(key)) { seen.add(key); snapCache.push({ x: c.x, y: c.y, z }); }
      }
      // 에지가 놓인 직선 수집 (해시 대신 허용오차 클러스터링 — 부동소수점에 강건하게)
      const dx = b.x - a.x, dy = b.y - a.y;
      const len = Math.hypot(dx, dy);
      if (len < 0.5) continue;
      let ux = dx / len, uy = dy / len;
      if (ux < 0 || (Math.abs(ux) < 1e-6 && uy < 0)) { ux = -ux; uy = -uy; }
      let found = null;
      for (const l of lineCount) {
        if (Math.abs(ux * l.u.x + uy * l.u.y) < 0.99996) continue;       // 평행(0.5도 이내)
        const dist = Math.abs(-l.u.y * (a.x - l.A.x) + l.u.x * (a.y - l.A.y));
        if (dist > 0.08) continue;                                        // 같은 직선 위
        found = l; break;
      }
      if (found) found.count++;
      else lineCount.push({ A: { x: a.x, y: a.y }, u: { x: ux, y: uy }, count: 1 });
    }
  }
  creaseLines = lineCount.filter(r => r.count >= 2);
}

// 접는 선이 기존 접힌 선과 거의 겹치면 그 선에 정확히 스냅 → 접힌 걸 도로 펼 수 있음
function snapCrease(L0, u) {
  const COS_TOL = Math.cos(THREE.MathUtils.degToRad(6));
  for (const c of creaseLines) {
    if (Math.abs(u.x * c.u.x + u.y * c.u.y) < COS_TOL) continue;
    const wx = L0.x - c.A.x, wy = L0.y - c.A.y;
    if (Math.abs(-c.u.y * wx + c.u.x * wy) > 0.9) continue; // 선까지 거리
    const t = wx * c.u.x + wy * c.u.y;
    return { L0: { x: c.A.x + c.u.x * t, y: c.A.y + c.u.y * t }, u: { ...c.u }, snapped: true };
  }
  return { L0, u, snapped: false };
}

// 접기 드래그 중 추가 자석 목표 (잡은 점을 각 접힌 선에 반사한 위치 = 펴면 도착할 지점)
let dragSnapExtras = [];
function mirrorAcrossLine(P, A, u) {
  const wx = P.x - A.x, wy = P.y - A.y;
  const t = wx * u.x + wy * u.y;
  const ax = A.x + u.x * t, ay = A.y + u.y * t; // P의 수선의 발
  return { x: 2 * ax - P.x, y: 2 * ay - P.y };
}
function setUnfoldTargets(P) {
  dragSnapExtras = [];
  for (const c of creaseLines) {
    const m = mirrorAcrossLine(P, c.A, c.u);
    if (Math.hypot(m.x - P.x, m.y - P.y) > 1.2) dragSnapExtras.push({ x: m.x, y: m.y, z: 0.05 });
  }
}

const SNAP_PX = 20;
function snapPoint(p, e) {
  if (e.shiftKey) return { point: p, snapped: false };
  const rect = canvas.getBoundingClientRect();
  let best = null, bestD = Infinity;
  const v = new THREE.Vector3();
  for (const c of [...snapCache, ...dragSnapExtras]) {
    v.set(c.x, c.y, c.z).project(camera);
    const sx = (v.x + 1) / 2 * rect.width + rect.left;
    const sy = (-v.y + 1) / 2 * rect.height + rect.top;
    const d = Math.hypot(sx - e.clientX, sy - e.clientY);
    if (d < SNAP_PX && d < bestD) { bestD = d; best = c; }
  }
  return best ? { point: { x: best.x, y: best.y }, snapped: true } : { point: p, snapped: false };
}
function snapAngle(p0, p1) {
  const dx = p1.x - p0.x, dy = p1.y - p0.y;
  const len = Math.hypot(dx, dy);
  if (len < 0.5) return p1;
  const ang = Math.atan2(dy, dx);
  const step = Math.PI / 12;
  const snapped = Math.round(ang / step) * step;
  if (Math.abs(ang - snapped) < THREE.MathUtils.degToRad(4)) {
    return { x: p0.x + Math.cos(snapped) * len, y: p0.y + Math.sin(snapped) * len };
  }
  return p1;
}

const snapMarkerMat = new THREE.MeshBasicMaterial({ color: 0x33ff88, side: THREE.DoubleSide, depthTest: false, transparent: true, opacity: 0.95 });
const snapMarkerA = new THREE.Mesh(new THREE.RingGeometry(0.28, 0.5, 24), snapMarkerMat);
const snapMarkerB = new THREE.Mesh(new THREE.RingGeometry(0.28, 0.5, 24), snapMarkerMat);
snapMarkerA.renderOrder = snapMarkerB.renderOrder = 6000;
snapMarkerA.visible = snapMarkerB.visible = false;
scene.add(snapMarkerA, snapMarkerB);
function placeMarker(marker, p, on) {
  marker.visible = on;
  if (on) marker.position.set(p.x, p.y, maxLayer() * LAYER_EPS + 0.06);
}
function hideMarkers() { snapMarkerA.visible = snapMarkerB.visible = false; }

// ---------- 선/하이라이트 표시 ----------
function drawLineVisual(p0, p1, solidMat, dashMat) {
  clearLineVisual();
  const zTop = maxLayer() * LAYER_EPS + 0.05;
  const seg = new THREE.BufferGeometry().setFromPoints([
    new THREE.Vector3(p0.x, p0.y, zTop), new THREE.Vector3(p1.x, p1.y, zTop),
  ]);
  const line = new THREE.Line(seg, solidMat);
  line.userData.isLine = true;
  line.renderOrder = 5000;
  overlayGroup.add(line);
  const dx = p1.x - p0.x, dy = p1.y - p0.y;
  const len = Math.hypot(dx, dy) || 1;
  const ux = dx / len, uy = dy / len;
  const ext = new THREE.BufferGeometry().setFromPoints([
    new THREE.Vector3(p0.x - ux * 200, p0.y - uy * 200, zTop),
    new THREE.Vector3(p1.x + ux * 200, p1.y + uy * 200, zTop),
  ]);
  const dash = new THREE.Line(ext, dashMat);
  dash.computeLineDistances();
  dash.userData.isLine = true;
  dash.renderOrder = 4999;
  overlayGroup.add(dash);
}
function clearLineVisual() {
  for (const c of [...overlayGroup.children]) {
    if (c.userData.isLine) { c.geometry?.dispose(); overlayGroup.remove(c); }
  }
}
function drawRectVisual(a, b, mat) {
  clearLineVisual();
  const zTop = maxLayer() * LAYER_EPS + 0.05;
  const pts = [
    new THREE.Vector3(a.x, a.y, zTop), new THREE.Vector3(b.x, a.y, zTop),
    new THREE.Vector3(b.x, b.y, zTop), new THREE.Vector3(a.x, b.y, zTop),
  ];
  const loop = new THREE.LineLoop(new THREE.BufferGeometry().setFromPoints(pts), mat);
  loop.userData.isLine = true;
  loop.renderOrder = 5000;
  overlayGroup.add(loop);
}
function showHighlight(pieces, mat = matHighlight) {
  clearHighlight();
  for (const f of pieces) {
    const geo = facetGeometry(f, f.layer * LAYER_EPS + 0.03);
    const mesh = new THREE.Mesh(geo, mat);
    mesh.userData.isHighlight = true;
    mesh.renderOrder = 4500;
    overlayGroup.add(mesh);
  }
}
function clearHighlight() {
  for (const c of [...overlayGroup.children]) {
    if (c.userData.isHighlight) { c.geometry?.dispose(); overlayGroup.remove(c); }
  }
}

// ---------- 조각 판정 ----------
function topFacetAt(p, pieceId = null) { // 점 아래 가장 위층 facet
  let best = null, bestLayer = -Infinity;
  for (const f of facets) {
    if (pieceId != null && f.pieceId !== pieceId) continue;
    const tp = f.pts.map(q => applyT(f.T, q));
    if (pointInConvex(p, tp) && f.layer > bestLayer) { bestLayer = f.layer; best = f; }
  }
  return best;
}
function pieceAt(p) {
  const f = topFacetAt(p);
  return f ? f.pieceId : null;
}

// ---------- 접기 연산 ----------
// 조각 pieceId를 직선(L0,u)으로 분할. 나머지 facet은 keep으로.
function splitPiece(L0, u, pieceId) {
  const n = { x: -u.y, y: u.x };
  const pos = [], neg = [], keep = [];
  for (const f of facets) {
    if (f.pieceId !== pieceId) { keep.push(f); continue; }
    const gvals = f.pts.map(p => {
      const tp = applyT(f.T, p);
      return (tp.x - L0.x) * n.x + (tp.y - L0.y) * n.y;
    });
    const pPos = clipPoly(f.pts, gvals, true);
    const pNeg = clipPoly(f.pts, gvals, false);
    if (pPos.length >= 3 && polyArea(pPos) > MIN_AREA) pos.push({ ...f, pts: pPos });
    if (pNeg.length >= 3 && polyArea(pNeg) > MIN_AREA) neg.push({ ...f, pts: pNeg });
  }
  if (pos.length === 0 || neg.length === 0) return null;
  return { pos, neg, keep, n };
}

// 접기 커밋: fold 조각들을 (L0,u) 반사, 층 재배치
function commitFoldPieces(stay, fold, keep, L0, u, dir) {
  const R = reflectAcross(L0, u);
  const stayLayers = stay.map(f => f.layer);
  const foldLayers = fold.map(f => f.layer);
  const maxStay = Math.max(...stayLayers), minStay = Math.min(...stayLayers);
  const maxFold = Math.max(...foldLayers), minFold = Math.min(...foldLayers);

  const out = [...keep, ...stay.map(f => ({ ...f }))];
  for (const f of fold) {
    const layer = dir === 'over'
      ? maxStay + 1 + (maxFold - f.layer)
      : minStay - 1 - (f.layer - minFold);
    out.push({ ...f, T: composeRT(R, f.T), layer });
  }
  const minL = Math.min(...out.map(f => f.layer));
  for (const f of out) f.layer -= minL;
  pushUndo();
  facets = out;
  compactLayers(); // 펴진 부분은 바닥으로 내려앉게
}

// ---------- 접기 제스처 (잡아서 끌기 — 실시간으로 따라 접힘) ----------
// P(잡은 점) → Q(현재 커서): 접는 선 = PQ의 수직이등분선, P쪽 플랩이 커서를 따라 넘어옴
let foldDrag = null;        // { P, pieceId }
let foldAnim = null;        // { t0, fromK, stay, fold, keep, L0, u, dir, sign } — 놓은 뒤 정착 애니메이션
const DRAG_K = 0.93;        // 드래그 중 플랩 각도 (180°보다 살짝 덜 접어 들려 있는 느낌)
let lastPreviewBuild = 0;

function computeFoldPre(P, Q, pieceId, creaseSnapOn = true) { // 순수 계산 (그리기 없음)
  const dx = Q.x - P.x, dy = Q.y - P.y;
  const len = Math.hypot(dx, dy);
  if (len < 0.6) return null;
  const nrm = { x: dx / len, y: dy / len };           // P→Q 방향 (접는 선의 법선)
  let L0 = { x: (P.x + Q.x) / 2, y: (P.y + Q.y) / 2 };
  let u = { x: -nrm.y, y: nrm.x };                     // 접는 선 방향
  let creaseSnapped = false;
  if (creaseSnapOn) {
    const cs = snapCrease(L0, u);
    if (cs.snapped) { L0 = cs.L0; u = cs.u; creaseSnapped = true; }
  }
  const s = splitPiece(L0, u, pieceId);
  if (!s) return null;
  const gP = (P.x - L0.x) * s.n.x + (P.y - L0.y) * s.n.y;
  if (Math.abs(gP) < 1e-6) return null; // 잡은 점이 접는 선 위 — 방향 불명
  return {
    stay: gP >= 0 ? s.neg : s.pos,
    fold: gP >= 0 ? s.pos : s.neg,
    keep: s.keep,
    L0, u,
    sign: gP >= 0 ? 1 : -1,
    creaseSnapped,
  };
}

// 펴기: 드래그(P→Q)가 기존 접힌 선을 가로지르면, 그 선에서 접힌 플랩 묶음만 도로 반사
// 플랩 판별: 잡은 최상단 facet과 "종이좌표 기준" 같은 쪽에 있는 facet들 (크리스는 facet 경계라 깨끗이 갈림)
function computeUnfoldPre(P, Q, pieceId) {
  const dxq = Q.x - P.x, dyq = Q.y - P.y;
  const lenq = Math.hypot(dxq, dyq);
  if (lenq < 0.6) return null;
  const ub = { x: -dyq / lenq, y: dxq / lenq }; // 이등분선(접는 선) 방향
  const COS_TOL = Math.cos(THREE.MathUtils.degToRad(35));
  let best = null, bestT = Infinity;
  for (const c of creaseLines) {
    if (Math.abs(ub.x * c.u.x + ub.y * c.u.y) < COS_TOL) continue;
    const nx = -c.u.y, ny = c.u.x;
    const sP = nx * (P.x - c.A.x) + ny * (P.y - c.A.y);
    const sQ = nx * (Q.x - c.A.x) + ny * (Q.y - c.A.y);
    if (sP * sQ >= -1e-9) continue; // PQ가 이 크리스를 가로지르지 않음
    const t = sP / (sP - sQ);
    if (t < bestT) { bestT = t; best = { c, sSign: sP >= 0 ? 1 : -1 }; }
  }
  if (!best) return null;
  const { c } = best;
  const F0 = topFacetAt(P, pieceId);
  if (!F0) return null;
  // 크리스를 종이좌표로 (같은 piece의 pts는 모두 원본 종이 좌표계)
  const inv = invertT(F0.T);
  const Ap = applyT(inv, c.A);
  const Bp = applyT(inv, { x: c.A.x + c.u.x, y: c.A.y + c.u.y });
  let ux = Bp.x - Ap.x, uy = Bp.y - Ap.y;
  const ul = Math.hypot(ux, uy); ux /= ul; uy /= ul;
  const npx = -uy, npy = ux;
  const cen = poly => {
    let x = 0, y = 0;
    for (const p of poly) { x += p.x; y += p.y; }
    return { x: x / poly.length, y: y / poly.length };
  };
  const c0 = cen(F0.pts);
  const s0 = Math.sign((c0.x - Ap.x) * npx + (c0.y - Ap.y) * npy);
  if (!s0) return null;
  const fold = [], stay = [], keep = [];
  for (const f of facets) {
    if (f.pieceId !== pieceId) { keep.push(f); continue; }
    const cf = cen(f.pts);
    const s = (cf.x - Ap.x) * npx + (cf.y - Ap.y) * npy;
    if (s * s0 > 0) fold.push({ ...f }); else stay.push({ ...f });
  }
  if (!fold.length || !stay.length) return null;
  return {
    stay, fold, keep,
    L0: { ...c.A }, u: { ...c.u },
    sign: best.sSign,
    creaseSnapped: true,
    isUnfold: true,
  };
}

function applyFoldMatrix(pre, k, dir) {
  const zTop = maxLayer() * LAYER_EPS;
  const hingeZ = dir === 'over' ? zTop / 2 + LAYER_EPS * 0.5 : -LAYER_EPS * 0.5;
  const axis = new THREE.Vector3(pre.u.x * pre.sign, pre.u.y * pre.sign, 0).normalize();
  const theta = Math.PI * k * (dir === 'over' ? 1 : -1);
  const M = new THREE.Matrix4()
    .makeTranslation(pre.L0.x, pre.L0.y, hingeZ)
    .multiply(new THREE.Matrix4().makeRotationAxis(axis, theta))
    .multiply(new THREE.Matrix4().makeTranslation(-pre.L0.x, -pre.L0.y, -hingeZ));
  previewGroup.matrix.copy(M);
}

// 드래그 중 실시간 미리보기: stay+keep은 고정, fold 플랩은 커서를 따라 접힌 상태로
function renderFoldDragPreview(pre) {
  const now = performance.now();
  if (now - lastPreviewBuild > 24) { // 지오메트리 재생성은 ~40fps로 제한
    lastPreviewBuild = now;
    clearGroup(paperGroup); clearGroup(previewGroup);
    for (const f of [...pre.keep, ...pre.stay]) buildFacetInto(paperGroup, f);
    for (const f of pre.fold) buildFacetInto(previewGroup, f);
  }
  applyFoldMatrix(pre, DRAG_K, foldDir);
  drawLineVisual(
    { x: pre.L0.x - pre.u.x * 6, y: pre.L0.y - pre.u.y * 6 },
    { x: pre.L0.x + pre.u.x * 6, y: pre.L0.y + pre.u.y * 6 },
    pre.creaseSnapped ? matCreaseLine : matFoldLine, matFoldDash
  );
}

function startFoldSettle(pre) { // 놓는 순간: 현재 각도 → 180° 로 짧게 정착
  clearGroup(paperGroup); clearGroup(previewGroup); clearGroup(overlayGroup);
  previewGroup.matrix.identity();
  for (const f of [...pre.keep, ...pre.stay]) buildFacetInto(paperGroup, f);
  for (const f of pre.fold) buildFacetInto(previewGroup, f);
  applyFoldMatrix(pre, DRAG_K, foldDir);
  foldAnim = { t0: performance.now(), fromK: DRAG_K, ...pre, dir: foldDir };
}

function finishFoldAnim() {
  const a = foldAnim;
  foldAnim = null;
  commitFoldPieces(a.stay, a.fold, a.keep, a.L0, a.u, a.dir);
  rebuildScene();
}

// ---------- 오리기 ----------
function cutAll(L0, u) {
  const n = { x: -u.y, y: u.x };
  const out = [];
  const sidesByPiece = new Map(); // pieceId -> {pos:bool, neg:bool}
  const parts = [];
  for (const f of facets) {
    const gvals = f.pts.map(p => {
      const tp = applyT(f.T, p);
      return (tp.x - L0.x) * n.x + (tp.y - L0.y) * n.y;
    });
    const pPos = clipPoly(f.pts, gvals, true);
    const pNeg = clipPoly(f.pts, gvals, false);
    const hasPos = pPos.length >= 3 && polyArea(pPos) > MIN_AREA;
    const hasNeg = pNeg.length >= 3 && polyArea(pNeg) > MIN_AREA;
    const rec = sidesByPiece.get(f.pieceId) || { pos: false, neg: false };
    rec.pos = rec.pos || hasPos; rec.neg = rec.neg || hasNeg;
    sidesByPiece.set(f.pieceId, rec);
    if (hasPos) parts.push({ ...f, pts: pPos, __side: 1 });
    if (hasNeg) parts.push({ ...f, pts: pNeg, __side: -1 });
  }
  // 실제로 잘린 조각이 있는지 (양쪽에 걸친 piece 존재 여부)
  let anySplit = false;
  for (const rec of sidesByPiece.values()) if (rec.pos && rec.neg) anySplit = true;
  if (!anySplit) return false;
  // 양쪽에 걸친 piece: neg쪽에 새 pieceId 부여
  let nid = nextPieceId();
  const newIdFor = new Map();
  for (const [pid, rec] of sidesByPiece) {
    if (rec.pos && rec.neg) newIdFor.set(pid, nid++);
  }
  for (const p of parts) {
    const mapped = (p.__side === -1 && newIdFor.has(p.pieceId)) ? newIdFor.get(p.pieceId) : p.pieceId;
    const { __side, ...rest } = p;
    out.push({ ...rest, pieceId: mapped });
  }
  pushUndo();
  facets = out;
  return true;
}

// 네모 영역 오려내기: 사각형 안쪽을 새 조각으로 분리 (나머지는 구멍 뚫린 채 유지)
function cutRectRegion(a, b) {
  const x0 = Math.min(a.x, b.x), x1 = Math.max(a.x, b.x);
  const y0 = Math.min(a.y, b.y), y1 = Math.max(a.y, b.y);
  if (x1 - x0 < 0.5 || y1 - y0 < 0.5) return null;
  const planes = [p => x0 - p.x, p => p.x - x1, p => y0 - p.y, p => p.y - y1]; // g>0 = 바깥
  const inside = [], outside = [];
  for (const f of facets) {
    let curPts = f.pts; // 바깥쪽을 한 변씩 떼어내며 볼록 분할
    for (const g of planes) {
      if (curPts.length < 3) break;
      const gvals = curPts.map(p => g(applyT(f.T, p)));
      const outPoly = clipPoly(curPts, gvals, true);
      if (outPoly.length >= 3 && polyArea(outPoly) > MIN_AREA) outside.push({ ...f, pts: outPoly });
      curPts = clipPoly(curPts, gvals, false);
    }
    if (curPts.length >= 3 && polyArea(curPts) > MIN_AREA) inside.push({ ...f, pts: curPts });
  }
  if (!inside.length) return null;
  // 안팎에 걸친 piece만 분리 (전부 안쪽이면 이미 통째 조각이므로 의미 없음)
  const insidePieces = new Set(inside.map(f => f.pieceId));
  const outsidePieces = new Set(outside.map(f => f.pieceId));
  const newIdFor = new Map();
  const newIds = [];
  let nid = nextPieceId();
  for (const pid of insidePieces) {
    if (outsidePieces.has(pid)) { newIdFor.set(pid, nid); newIds.push(nid); nid++; }
  }
  if (!newIds.length) return null;
  pushUndo();
  facets = [
    ...outside,
    ...inside.map(f => newIdFor.has(f.pieceId) ? { ...f, pieceId: newIdFor.get(f.pieceId) } : f),
  ];
  return newIds;
}

// ---------- 옮기기 ----------
let moveDrag = null; // { pieceId, start, cur }

function bakeMove(pieceId, dx, dy) {
  pushUndo();
  // 옮긴 조각을 다른 모든 조각 위로 올림 (집었다 놓는 느낌)
  const others = facets.filter(f => f.pieceId !== pieceId);
  const mine = facets.filter(f => f.pieceId === pieceId);
  const base = others.length ? Math.max(...others.map(f => f.layer)) + 1 : 0;
  const minMine = Math.min(...mine.map(f => f.layer));
  for (const f of mine) {
    f.T = translateT(f.T, dx, dy);
    f.layer = base + (f.layer - minMine);
  }
  compactLayers();
}

function rotatePiece(pieceId, deg) {
  const mine = facets.filter(f => f.pieceId === pieceId);
  if (!mine.length) return;
  // 조각 중심 계산
  let cx = 0, cy = 0, cnt = 0;
  for (const f of mine) {
    for (const p of f.pts) {
      const tp = applyT(f.T, p);
      cx += tp.x; cy += tp.y; cnt++;
    }
  }
  const R = rotationAround({ x: cx / cnt, y: cy / cnt }, THREE.MathUtils.degToRad(deg));
  pushUndo();
  for (const f of mine) f.T = composeRT(R, f.T);
  compactLayers();
}

// ---------- UI ----------
const hint = document.getElementById('hint');
const dirPanel = document.getElementById('dirPanel');
const rotPanel = document.getElementById('rotPanel');
const cutPanel = document.getElementById('cutPanel');
let cutShape = 'line'; // line | rect
const btnFold = document.getElementById('btnFold');
const btnCut = document.getElementById('btnCut');
const btnMove = document.getElementById('btnMove');
const btnLight = document.getElementById('btnLight');
const dirOverBtn = document.getElementById('dirOver');
const dirUnderBtn = document.getElementById('dirUnder');

function setHint(t) { hint.textContent = t; }

const HINTS = {
  view: '드래그로 회전 · 휠/핀치로 확대축소',
  fold: '잡고 끌면 접혀요 · 접힌 부분을 반대로 끌면 펴져요(초록 선) · 우클릭 회전',
  cut: '드래그로 자를 선을 그으세요 · 우클릭 회전',
  cutRect: '네모를 드래그로 그리면 그 부분이 뚝 떼어져요 · 우클릭 회전',
  move: '조각을 잡아 끌어서 옮기세요 · 우클릭 회전',
};
function cutHint() { return cutShape === 'rect' ? HINTS.cutRect : HINTS.cut; }

function setMode(m) {
  if (foldAnim) return; // 접히는 중엔 무시
  if (spreadMode && m !== 'view') return; // 펼침 상태에선 도구 잠금
  if (typeof overlayOpen !== 'undefined' && overlayOpen && m !== 'view') closeOverlay(); // 도구 켜면 겹치기 종료
  mode = m;
  dirPanel.classList.toggle('hidden', m !== 'fold');
  rotPanel.classList.toggle('hidden', m !== 'move');
  cutPanel.classList.toggle('hidden', m !== 'cut');
  btnFold.classList.toggle('active', m === 'fold');
  btnCut.classList.toggle('active', m === 'cut');
  btnMove.classList.toggle('active', m === 'move');
  setControlsForTool(m !== 'view');
  canvas.style.cursor = (m === 'fold' || m === 'move') ? 'grab' : (m === 'cut') ? 'crosshair' : 'default';
  hideMarkers(); clearLineVisual(); clearHighlight();
  foldDrag = null; moveDrag = null; cutDrag = null; dragSnapExtras = [];
  setHint(m === 'cut' ? cutHint() : HINTS[m]);
  if (m === 'fold' || m === 'cut') alignTopDown();
}

function toggleTool(m) { setMode(mode === m ? 'view' : m); }
btnFold.addEventListener('click', () => toggleTool('fold'));
btnCut.addEventListener('click', () => toggleTool('cut'));
btnMove.addEventListener('click', () => toggleTool('move'));

document.getElementById('btnUndo').addEventListener('click', () => {
  if (foldAnim) return;
  if (undoStack.length === 0) { setHint('되돌릴 동작이 없어요'); return; }
  facets = undoStack.pop();
  selectedPiece = null;
  rebuildScene();
});

document.getElementById('btnReset').addEventListener('click', () => {
  if (foldAnim) return;
  if (facets.length === 1) return;
  pushUndo();
  facets = [initialFacet()];
  selectedPiece = null;
  rebuildScene();
});

document.getElementById('btnFlip').addEventListener('click', () => startFlip());

btnLight.addEventListener('click', () => {
  lightMode = !lightMode;
  btnLight.classList.toggle('active', lightMode);
  applyMaterialMode();
});

dirOverBtn.addEventListener('click', () => { foldDir = 'over'; dirOverBtn.classList.add('active'); dirUnderBtn.classList.remove('active'); });
dirUnderBtn.addEventListener('click', () => { foldDir = 'under'; dirUnderBtn.classList.add('active'); dirOverBtn.classList.remove('active'); });

const cutLineBtn = document.getElementById('cutLine');
const cutRectBtn = document.getElementById('cutRect');
cutLineBtn.addEventListener('click', () => { cutShape = 'line'; cutLineBtn.classList.add('active'); cutRectBtn.classList.remove('active'); setHint(cutHint()); });
cutRectBtn.addEventListener('click', () => { cutShape = 'rect'; cutRectBtn.classList.add('active'); cutLineBtn.classList.remove('active'); setHint(cutHint()); });

document.getElementById('rotCCW').addEventListener('click', () => {
  if (selectedPiece == null) { setHint('먼저 조각을 클릭/드래그해서 선택하세요'); return; }
  rotatePiece(selectedPiece, 15); rebuildScene(); highlightSelected();
});
document.getElementById('rotCW').addEventListener('click', () => {
  if (selectedPiece == null) { setHint('먼저 조각을 클릭/드래그해서 선택하세요'); return; }
  rotatePiece(selectedPiece, -15); rebuildScene(); highlightSelected();
});

function highlightSelected() {
  if (selectedPiece == null) return;
  showHighlight(facets.filter(f => f.pieceId === selectedPiece), matPieceSel);
}

// 이미지 업로드
const fileFront = document.getElementById('fileFront');
const fileBack = document.getElementById('fileBack');
document.getElementById('btnFront').addEventListener('click', () => fileFront.click());
document.getElementById('btnBack').addEventListener('click', () => fileBack.click());

function loadImageFile(file) {
  return new Promise((res, rej) => {
    const img = new Image();
    img.onload = () => res(img);
    img.onerror = rej;
    img.src = URL.createObjectURL(file);
  });
}
fileFront.addEventListener('change', async () => {
  const f = fileFront.files[0];
  if (!f) return;
  try {
    frontImg = await loadImageFile(f);
    const aspect = frontImg.naturalWidth / frontImg.naturalHeight;
    paperH = BASE_H;
    paperW = Math.min(60, Math.max(5, BASE_H * aspect));
    facets = [initialFacet()];
    undoStack.length = 0;
    selectedPiece = null;
    rebuildTextures();
    rebuildScene();
    setHint('앞면 이미지 적용됨 (접기 상태 초기화)');
  } catch { setHint('이미지를 불러오지 못했어요'); }
  fileFront.value = '';
});
fileBack.addEventListener('change', async () => {
  const f = fileBack.files[0];
  if (!f) return;
  try {
    backImg = await loadImageFile(f);
    rebuildTextures();
    setHint('뒷면 이미지 적용됨');
  } catch { setHint('이미지를 불러오지 못했어요'); }
  fileBack.value = '';
});

// ---------- 겹치기 (클리어파일처럼 반투명하게 다른 자료를 겹쳐 대보기) ----------
const btnOverlay = document.getElementById('btnOverlay');
const overlayPanel = document.getElementById('overlayPanel');
const overlaySrcs = document.getElementById('overlaySrcs');
const ovMirrorBtn = document.getElementById('ovMirror');
const ovScale = document.getElementById('ovScale');
let overlay = null; // { mesh, srcIdx, x, y, scale, mirror, baseW, baseH }
let overlayOpen = false; // 패널 열림 (자료는 플레이어가 직접 선택해야 겹쳐짐)
let ovDrag = null;
const overlayTexCache = new Map();

function overlayTexture(idx, mirror) {
  const key = idx + (mirror ? 'm' : '');
  if (overlayTexCache.has(key)) return overlayTexCache.get(key);
  const img = papers[idx].front;
  const sc = Math.min(1, 1400 / Math.max(img.naturalWidth, img.naturalHeight));
  const c = document.createElement('canvas');
  c.width = Math.max(32, Math.round(img.naturalWidth * sc));
  c.height = Math.max(32, Math.round(img.naturalHeight * sc));
  const g = c.getContext('2d');
  if (mirror) { g.translate(c.width, 0); g.scale(-1, 1); }
  g.drawImage(img, 0, 0, c.width, c.height);
  // 밝은 배경 -> 투명 (실제 클리어 파일처럼 그림만 남김)
  const id = g.getImageData(0, 0, c.width, c.height);
  const d = id.data;
  for (let i = 0; i < d.length; i += 4) {
    const lum = 0.299 * d[i] + 0.587 * d[i + 1] + 0.114 * d[i + 2];
    d[i + 3] = Math.round(Math.max(0, Math.min(1, (215 - lum) / 90)) * 255);
  }
  g.putImageData(id, 0, 0);
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  overlayTexCache.set(key, t);
  return t;
}

function removeOverlayMesh() {
  if (overlay?.mesh) {
    scene.remove(overlay.mesh);
    overlay.mesh.geometry.dispose();
    overlay.mesh.material.dispose();
    overlay.mesh = null;
  }
}
function buildOverlayMesh() {
  removeOverlayMesh();
  const mat = new THREE.MeshBasicMaterial({
    map: overlayTexture(overlay.srcIdx, overlay.mirror),
    transparent: true, depthTest: false, side: THREE.DoubleSide,
  });
  const mesh = new THREE.Mesh(new THREE.PlaneGeometry(overlay.baseW, overlay.baseH), mat);
  mesh.renderOrder = 7000;
  overlay.mesh = mesh;
  scene.add(mesh);
  updateOverlayMesh();
}
function updateOverlayMesh() {
  if (!overlay?.mesh) return;
  overlay.mesh.position.set(overlay.x, overlay.y, maxLayer() * LAYER_EPS + 1.0);
  overlay.mesh.scale.set(overlay.scale, overlay.scale, 1);
}
function fitOverlayToPaper() { // 종이에 끼운 것처럼 정확히 겹치기
  if (!overlay) return;
  overlay.x = 0; overlay.y = 0;
  overlay.scale = paperH / overlay.baseH;
  ovScale.value = Math.round(overlay.scale * 100);
  updateOverlayMesh();
}
function setOverlaySrc(idx) {
  if (overlay && overlay.srcIdx === idx) { // 같은 번호를 다시 누르면 치우기
    removeOverlayMesh();
    overlay = null; ovDrag = null;
    for (const b of overlaySrcs.children) b.classList.remove('active');
    setControlsForTool(false);
    setHint('겹쳐 볼 자료의 번호를 선택하세요');
    return;
  }
  const img = papers[idx].front;
  const h = 22;
  overlay = {
    srcIdx: idx,
    x: 0, y: 0,
    scale: 1,
    mirror: overlay?.mirror ?? false,
    baseW: h * (img.naturalWidth / img.naturalHeight), baseH: h,
    mesh: null,
  };
  buildOverlayMesh();
  fitOverlayToPaper(); // 선택하면 종이 크기에 딱 맞춰 겹침 (파일에 끼운 상태)
  for (const b of overlaySrcs.children) b.classList.toggle('active', +b.dataset.idx === idx);
  setControlsForTool(true); // 좌드래그 = 오버레이 이동, 우클릭 = 회전
  setHint('드래그로 움직이고 슬라이더로 크기 조절 · 우클릭 회전');
}
function openOverlay() {
  setMode('view');
  overlayOpen = true;
  btnOverlay.classList.add('active');
  overlayPanel.classList.remove('hidden');
  overlaySrcs.innerHTML = '';
  let n = 0;
  papers.forEach((p, i) => {
    const label = p.isKit ? '🗂' : `${++n}`;
    if (!p.front) return;
    const b = document.createElement('button');
    b.textContent = label;
    b.dataset.idx = i;
    b.addEventListener('click', () => setOverlaySrc(i));
    overlaySrcs.appendChild(b);
  });
  // 자료 자동 선택 없음 — 무엇을 겹칠지는 플레이어의 몫
  setHint('겹쳐 볼 자료의 번호를 선택하세요');
}
function closeOverlay() {
  removeOverlayMesh();
  overlay = null; ovDrag = null; overlayOpen = false;
  btnOverlay.classList.remove('active');
  overlayPanel.classList.add('hidden');
  setControlsForTool(mode !== 'view');
  setHint(HINTS[mode] || HINTS.view);
}
btnOverlay.addEventListener('click', () => { if (overlayOpen) closeOverlay(); else openOverlay(); });
document.getElementById('ovClose').addEventListener('click', closeOverlay);
document.getElementById('ovFit').addEventListener('click', fitOverlayToPaper);
ovMirrorBtn.addEventListener('click', () => {
  if (!overlay) return;
  overlay.mirror = !overlay.mirror;
  ovMirrorBtn.classList.toggle('active', overlay.mirror);
  buildOverlayMesh();
});
ovScale.addEventListener('input', () => {
  if (!overlay) return;
  overlay.scale = parseInt(ovScale.value, 10) / 100;
  updateOverlayMesh();
});

// ---------- 포인터 ----------
const raycaster = new THREE.Raycaster();
const tablePlane = new THREE.Plane(new THREE.Vector3(0, 0, 1), 0);
const _v3 = new THREE.Vector3();

function pointerToTable(e) {
  const rect = canvas.getBoundingClientRect();
  const nx = ((e.clientX - rect.left) / rect.width) * 2 - 1;
  const ny = -((e.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera({ x: nx, y: ny }, camera);
  const hit = raycaster.ray.intersectPlane(tablePlane, _v3);
  return hit ? { x: hit.x, y: hit.y } : null;
}

let cutDrag = null; // { p0, p1 }
let lastFoldPreview = null;

canvas.addEventListener('pointerdown', (e) => {
  if (e.button !== 0 || !e.isPrimary || foldAnim) return;
  if (spreadMode) { spreadDown = { x: e.clientX, y: e.clientY }; return; }
  if (overlay) { // 겹치기 중: 좌드래그 = 오버레이 이동
    const p = pointerToTable(e);
    if (!p) return;
    ovDrag = { p0: p, x0: overlay.x, y0: overlay.y };
    try { canvas.setPointerCapture(e.pointerId); } catch {}
    return;
  }
  const raw = pointerToTable(e);
  if (!raw) return;

  if (mode === 'fold') {
    const s = snapPoint(raw, e);
    const pid = pieceAt(s.point) ?? pieceAt(raw);
    if (pid == null) return;
    foldDrag = { P: s.point, pieceId: pid };
    setUnfoldTargets(s.point); // 펴기 도착점(거울상)을 자석 목표로
    placeMarker(snapMarkerA, s.point, s.snapped);
    try { canvas.setPointerCapture(e.pointerId); } catch {}
    canvas.style.cursor = 'grabbing';
  } else if (mode === 'cut') {
    const s = snapPoint(raw, e);
    cutDrag = { p0: s.point, p1: s.point };
    placeMarker(snapMarkerA, s.point, s.snapped);
    try { canvas.setPointerCapture(e.pointerId); } catch {}
  } else if (mode === 'move') {
    const pid = pieceAt(raw);
    if (pid == null) return;
    selectedPiece = pid;
    moveDrag = { pieceId: pid, start: raw, cur: raw };
    rebuildScene(f => f.pieceId === pid); // 잡은 조각을 previewGroup으로
    highlightSelected();
    try { canvas.setPointerCapture(e.pointerId); } catch {}
    canvas.style.cursor = 'grabbing';
  }
});

canvas.addEventListener('pointermove', (e) => {
  if (foldAnim) return;
  if (ovDrag && overlay) {
    const p = pointerToTable(e);
    if (!p) return;
    overlay.x = ovDrag.x0 + (p.x - ovDrag.p0.x);
    overlay.y = ovDrag.y0 + (p.y - ovDrag.p0.y);
    updateOverlayMesh();
    return;
  }
  const raw = pointerToTable(e);
  if (!raw) return;

  if (mode === 'fold' && foldDrag) {
    const s = snapPoint(raw, e);
    placeMarker(snapMarkerB, s.point, s.snapped);
    const pre = (!e.shiftKey && computeUnfoldPre(foldDrag.P, s.point, foldDrag.pieceId))
      || computeFoldPre(foldDrag.P, s.point, foldDrag.pieceId, !e.shiftKey);
    if (pre) {
      renderFoldDragPreview(pre); // 플랩이 커서를 따라 실시간으로 접힘
    } else if (lastFoldPreview) {
      rebuildScene(); clearLineVisual(); // 유효 범위를 벗어나면 원상 표시
    }
    lastFoldPreview = pre;
  } else if (mode === 'fold') {
    const s = snapPoint(raw, e);
    placeMarker(snapMarkerA, s.point, s.snapped);
  } else if (mode === 'cut' && cutDrag) {
    const s = snapPoint(raw, e);
    if (cutShape === 'rect') {
      cutDrag.p1 = s.point;
      placeMarker(snapMarkerB, cutDrag.p1, s.snapped);
      drawRectVisual(cutDrag.p0, cutDrag.p1, matCutLine);
    } else {
      cutDrag.p1 = s.snapped ? s.point : snapAngle(cutDrag.p0, s.point);
      placeMarker(snapMarkerB, cutDrag.p1, s.snapped);
      drawLineVisual(cutDrag.p0, cutDrag.p1, matCutLine, matCutDash);
    }
  } else if (mode === 'cut') {
    const s = snapPoint(raw, e);
    placeMarker(snapMarkerA, s.point, s.snapped);
  } else if (mode === 'move' && moveDrag) {
    moveDrag.cur = raw;
    const dx = raw.x - moveDrag.start.x, dy = raw.y - moveDrag.start.y;
    previewGroup.matrix.makeTranslation(dx, dy, 1.2); // 살짝 들어올린 느낌
  }
});

canvas.addEventListener('pointerup', (e) => {
  if (ovDrag) { ovDrag = null; return; }
  if (spreadMode && spreadDown) {
    const moved = Math.hypot(e.clientX - spreadDown.x, e.clientY - spreadDown.y);
    spreadDown = null;
    if (moved > 8) return; // 회전 드래그였음
    const rect = canvas.getBoundingClientRect();
    raycaster.setFromCamera({
      x: ((e.clientX - rect.left) / rect.width) * 2 - 1,
      y: -((e.clientY - rect.top) / rect.height) * 2 + 1,
    }, camera);
    const hits = raycaster.intersectObjects(spreadGroup.children)
      .filter(h => h.object.userData.paperIdx != null);
    if (hits.length) exitSpread(hits[0].object.userData.paperIdx);
    return;
  }
  if (mode === 'fold' && foldDrag) {
    const pre = lastFoldPreview;
    foldDrag = null; lastFoldPreview = null; dragSnapExtras = [];
    hideMarkers(); clearLineVisual(); clearHighlight();
    canvas.style.cursor = 'grab';
    if (pre) startFoldSettle(pre);
    else rebuildScene();
  } else if (mode === 'cut' && cutDrag) {
    const { p0, p1 } = cutDrag;
    cutDrag = null;
    hideMarkers(); clearLineVisual();
    if (cutShape === 'rect') {
      const newIds = cutRectRegion(p0, p1);
      if (newIds) {
        rebuildScene();
        selectedPiece = newIds[0];
        setMode('move'); // 바로 집어서 떼어놓을 수 있게
        highlightSelected();
        setHint('뚝! 떼어낸 조각을 끌어서 옮겨보세요');
      } else {
        setHint('오려낼 부분이 종이 위에 오게 네모를 그려주세요');
      }
    } else {
      const len = Math.hypot(p1.x - p0.x, p1.y - p0.y);
      if (len < 0.8) return;
      const u = { x: (p1.x - p0.x) / len, y: (p1.y - p0.y) / len };
      if (cutAll(p0, u)) {
        rebuildScene();
        setHint('싹둑! ✋ 옮기기로 조각을 움직여보세요');
      } else {
        setHint('선이 종이를 지나야 잘려요');
      }
    }
  } else if (mode === 'move' && moveDrag) {
    const { pieceId, start, cur } = moveDrag;
    moveDrag = null;
    canvas.style.cursor = 'grab';
    const dx = cur.x - start.x, dy = cur.y - start.y;
    if (Math.hypot(dx, dy) > 0.15) bakeMove(pieceId, dx, dy);
    rebuildScene();
    highlightSelected();
  }
});

// ---------- 디버그/테스트 API ----------
window.__fold = {
  get facets() { return facets; },
  get mode() { return mode; },
  count() { return facets.length; },
  layers() { return facets.map(f => f.layer); },
  pieces() { return [...new Set(facets.map(f => f.pieceId))]; },
  grabFold(px, py, qx, qy, dir = 'over') { // 잡아 끌기 접기/펴기 (즉시 커밋)
    const pid = pieceAt({ x: px, y: py });
    if (pid == null) return false;
    const P = { x: px, y: py }, Q = { x: qx, y: qy };
    const pre = computeUnfoldPre(P, Q, pid) || computeFoldPre(P, Q, pid);
    if (!pre) return false;
    commitFoldPieces(pre.stay, pre.fold, pre.keep, pre.L0, pre.u, dir);
    rebuildScene();
    return true;
  },
  cut(x1, y1, x2, y2) {
    const len = Math.hypot(x2 - x1, y2 - y1);
    const u = { x: (x2 - x1) / len, y: (y2 - y1) / len };
    const ok = cutAll({ x: x1, y: y1 }, u);
    if (ok) rebuildScene();
    return ok;
  },
  cutRect(x0, y0, x1, y1) {
    const ids = cutRectRegion({ x: x0, y: y0 }, { x: x1, y: y1 });
    if (ids) rebuildScene();
    return ids;
  },
  movePiece(pid, dx, dy) { bakeMove(pid, dx, dy); rebuildScene(); },
  rotate(pid, deg) { rotatePiece(pid, deg); rebuildScene(); },
  pieceAt(x, y) { return pieceAt({ x, y }); },
  undo() {
    if (!undoStack.length) return false;
    facets = undoStack.pop(); selectedPiece = null; rebuildScene(); return true;
  },
  reset() { pushUndo(); facets = [initialFacet()]; selectedPiece = null; rebuildScene(); },
  setLight(on) { lightMode = on; applyMaterialMode(); },
  camPos() { return camera.position.toArray().map(v => Math.round(v * 10) / 10); },
  flipNow() {
    startFlip();
    if (flipAnim) { setPolar(flipAnim.r, flipAnim.to, flipAnim.theta); flipAnim = null; }
  },
  snapAt(x, y) { return snapCache.filter(c => Math.hypot(c.x - x, c.y - y) < 2); },
  creases() { return creaseLines.map(c => ({ A: c.A, u: c.u, count: c.count })); },
};

// ---------- 시작 ----------
rebuildTextures();
rebuildScene();
setMode('view');

// ---------- 정보(종이) 여러 개: assets/1-front.*, 1-back.*, 2-front.* ... 자동 발견 ----------
let papers = [];              // [{ front, back }]
let currentPaper = 0;
const paperStates = new Map(); // idx -> { facets, undo, paperW, frontImg, backImg }
const paperBar = document.getElementById('paperBar');

let openMode = false; // 개봉 상태 (N-open.* 이미지 표시 중)
let btnOpen = null;

// ---------- 키트(클리어파일) 펼치기 ----------
// assets/0-front.* 이 있으면 첫 화면 = 키트. 개봉하면 자료들이 퍼져 나옴
let revealed = false;    // 개봉해서 정보 탭이 공개됨
let spreadAnim = null;
let spreadDown = null;
const spreadGroup = new THREE.Group();
scene.add(spreadGroup);
const spreadTexCache = new Map();

const SPREAD_SLOTS = [
  { x: -12, y: 7, r: -8 }, { x: 12, y: 8, r: 6 }, { x: -12, y: -8, r: 5 },
  { x: 13, y: -7, r: -5 }, { x: 0, y: 13, r: 3 }, { x: 0, y: -13, r: -4 },
  { x: -22, y: 0, r: 10 }, { x: 22, y: 0, r: -9 }, { x: -20, y: 13, r: 7 },
  { x: 20, y: -13, r: -7 }, { x: 20, y: 13, r: 9 }, { x: -20, y: -13, r: -9 },
];

function spreadTexture(key, img) {
  if (spreadTexCache.has(key)) return spreadTexCache.get(key);
  const scale = Math.min(1, 1024 / Math.max(img.naturalWidth, img.naturalHeight));
  const c = document.createElement('canvas');
  c.width = Math.max(32, Math.round(img.naturalWidth * scale));
  c.height = Math.max(32, Math.round(img.naturalHeight * scale));
  c.getContext('2d').drawImage(img, 0, 0, c.width, c.height);
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  spreadTexCache.set(key, t);
  return t;
}

function enterSpread() {
  if (overlayOpen) closeOverlay();
  spreadMode = true;
  revealed = true;
  paperGroup.visible = previewGroup.visible = overlayGroup.visible = false;
  hideMarkers();
  clearGroup(spreadGroup);
  // 가운데엔 빈 클리어파일(키트의 open 이미지)이 남음
  const kit = papers.find(p => p.isKit);
  if (kit?.open) {
    const img = kit.open;
    const h = 19;
    const w = h * (img.naturalWidth / img.naturalHeight);
    const center = new THREE.Mesh(
      new THREE.PlaneGeometry(w, h),
      new THREE.MeshBasicMaterial({ map: spreadTexture('kit-open', img), side: THREE.DoubleSide })
    );
    center.position.set(0, 0, 0.05);
    spreadGroup.add(center);
  }
  const infos = papers.map((p, i) => ({ p, i })).filter(x => !x.p.isKit && x.p.front);
  infos.forEach((x, k) => {
    const img = x.p.front;
    const h = 15;
    const w = h * (img.naturalWidth / img.naturalHeight);
    const mesh = new THREE.Mesh(
      new THREE.PlaneGeometry(w, h),
      new THREE.MeshBasicMaterial({ map: spreadTexture('p' + x.i, img), side: THREE.DoubleSide })
    );
    mesh.userData = { paperIdx: x.i, slot: SPREAD_SLOTS[k % SPREAD_SLOTS.length] };
    mesh.position.set(0, 0, 0.3 + k * 0.06);
    spreadGroup.add(mesh);
  });
  spreadGroup.visible = true;
  spreadAnim = { t0: performance.now() };
  alignTopDown();
  // 세로 화면(폰)에서도 퍼진 자료가 전부 보이도록 카메라 거리를 화면 비율에 맞춤
  if (flipAnim) {
    const t = Math.tan(THREE.MathUtils.degToRad(camera.fov / 2));
    flipAnim.r = Math.max(52, 23 / t, 32 / (t * camera.aspect));
  }
  updatePaperBarUI();
  syncOpenBtn();
  setHint('자료를 클릭하면 자세히 볼 수 있어요');
}

function exitSpread(toIdx = null) {
  spreadMode = false;
  spreadAnim = null;
  clearGroup(spreadGroup);
  paperGroup.visible = previewGroup.visible = overlayGroup.visible = true;
  if (toIdx != null && toIdx !== currentPaper) {
    switchPaper(toIdx);
  } else {
    updatePaperBarUI();
    syncOpenBtn();
    setHint(HINTS.view);
  }
}

function applyPaperImages() { // frontImg/backImg 기준으로 종이 크기 초기화
  paperH = BASE_H;
  paperW = frontImg
    ? Math.min(60, Math.max(5, BASE_H * (frontImg.naturalWidth / frontImg.naturalHeight)))
    : 21.0;
}

function applyModeImages() { // 현재 정보의 닫힘/개봉 상태에 맞는 이미지 적용
  const p = papers[currentPaper] || { front: null, back: null, open: null };
  frontImg = openMode ? (p.open || p.front) : p.front;
  backImg = openMode ? null : p.back;
  applyPaperImages();
}

function saveCurrentPaperState() {
  paperStates.set(currentPaper, {
    facets: structuredClone(facets),
    undo: structuredClone(undoStack),
    paperW, frontImg, backImg, openMode,
  });
}

function syncOpenBtn() {
  if (!btnOpen) return;
  const p = papers[currentPaper];
  if (p?.isKit) {
    btnOpen.classList.remove('hidden');
    btnOpen.textContent = spreadMode ? '🗂 모으기' : '📦 개봉';
  } else {
    btnOpen.classList.toggle('hidden', !p?.open);
    btnOpen.textContent = openMode ? '📦 닫기' : '📦 개봉';
  }
}

function updatePaperBarUI() { // 키트 있으면 개봉 전까지 정보 탭 숨김
  const kit = papers.some(p => p.isKit);
  for (let i = 0; i < papers.length && i < paperBar.children.length; i++) {
    const chip = paperBar.children[i];
    chip.classList.toggle('locked', kit && !revealed && !papers[i].isKit);
    chip.classList.toggle('active', i === currentPaper && !spreadMode);
  }
}

function switchPaper(idx, initial = false) {
  if (!initial && overlayOpen) closeOverlay();
  if (spreadMode) { // 펼침 상태에서 탭 클릭 → 펼침 종료 후 이동
    spreadMode = false;
    spreadAnim = null;
    clearGroup(spreadGroup);
    paperGroup.visible = previewGroup.visible = overlayGroup.visible = true;
  }
  if (!initial) {
    if (idx === currentPaper) return;
    saveCurrentPaperState();
  }
  currentPaper = idx;
  const st = paperStates.get(idx);
  if (st) {
    facets = structuredClone(st.facets);
    undoStack.length = 0;
    for (const u of st.undo) undoStack.push(u);
    paperW = st.paperW; paperH = BASE_H;
    frontImg = st.frontImg; backImg = st.backImg;
    openMode = st.openMode ?? false;
  } else {
    openMode = false;
    applyModeImages();
    facets = [initialFacet()];
    undoStack.length = 0;
  }
  selectedPiece = null;
  rebuildTextures();
  rebuildScene();
  updatePaperBarUI();
  syncOpenBtn();
}

function toggleOpen() {
  if (papers[currentPaper]?.isKit) { // 키트: 개봉 = 자료 펼치기
    if (spreadMode) exitSpread();
    else enterSpread();
    return;
  }
  openMode = !openMode;
  applyModeImages();
  facets = [initialFacet()];
  undoStack.length = 0;
  selectedPiece = null;
  rebuildTextures();
  rebuildScene();
  syncOpenBtn();
  setHint(openMode ? '내용물을 꺼냈어요 — 📦 닫기로 되돌릴 수 있어요' : HINTS[mode] || HINTS.view);
}

function buildPaperBar() {
  paperBar.innerHTML = '';
  const anyOpen = papers.some(p => p.open || p.isKit);
  paperBar.classList.toggle('hidden', papers.length <= 1 && !anyOpen);
  let n = 0;
  papers.forEach((p, i) => {
    const b = document.createElement('button');
    b.textContent = p.isKit ? '🗂 키트' : `정보 ${++n}`;
    b.addEventListener('click', () => switchPaper(i));
    paperBar.appendChild(b);
  });
  btnOpen = document.createElement('button');
  btnOpen.className = 'openBtn hidden';
  btnOpen.textContent = '📦 개봉';
  btnOpen.addEventListener('click', toggleOpen);
  paperBar.appendChild(btnOpen);
  updatePaperBarUI();
}

(async function discoverPapers() {
  const tryImg = (srcs) => new Promise(res => {
    let settled = false;
    const done = v => { if (!settled) { settled = true; res(v); } };
    const next = (i) => {
      if (i >= srcs.length) return done(null);
      const img = new Image();
      img.onload = () => done(img);
      img.onerror = () => next(i + 1);
      img.src = srcs[i];
    };
    next(0);
    setTimeout(() => done(null), 8000); // 응답 없는 요청에 전체가 매달리지 않게
  });
  const exts = ['jpg', 'png', 'webp', 'jpeg'];
  const results = await Promise.all(Array.from({ length: 13 }, (_, i) => Promise.all([
    tryImg(exts.map(e => `assets/${i}-front.${e}`)),
    tryImg(exts.map(e => `assets/${i}-back.${e}`)),
    tryImg(exts.map(e => `assets/${i}-open.${e}`)),
  ])));
  papers = results
    .map(([f, b, o], i) => ({ front: f, back: b, open: o, isKit: i === 0 }))
    .filter(p => p.front);
  if (!papers.length) { // 구버전 호환: front.* / back.*
    const [f, b] = await Promise.all([
      tryImg(exts.map(e => `assets/front.${e}`)),
      tryImg(exts.map(e => `assets/back.${e}`)),
    ]);
    if (f || b) papers = [{ front: f, back: b, open: null, isKit: false }];
  }
  window.__discover = { found: papers.length };
  if (papers.length) {
    try {
      buildPaperBar();
      switchPaper(0, true);
    } catch (err) {
      window.__discover.err = String(err && err.stack || err);
    }
  }
})().catch(err => { window.__discover = { fatal: String(err && err.stack || err) }; });

function animate() {
  requestAnimationFrame(animate);
  if (flipAnim) {
    const k = Math.min(1, (performance.now() - flipAnim.t0) / 500);
    const e = k < 0.5 ? 2 * k * k : -1 + (4 - 2 * k) * k;
    const phi = flipAnim.from + (flipAnim.to - flipAnim.from) * e;
    setPolar(flipAnim.r, phi, flipAnim.theta);
    if (k >= 1) flipAnim = null;
  }
  if (foldAnim) {
    const t = Math.min(1, (performance.now() - foldAnim.t0) / FOLD_ANIM_MS);
    const k = foldAnim.fromK + (1 - foldAnim.fromK) * t;
    applyFoldMatrix(foldAnim, k, foldAnim.dir);
    if (t >= 1) finishFoldAnim();
  }
  if (spreadAnim) { // 자료가 사방으로 퍼지는 연출
    const k = Math.min(1, (performance.now() - spreadAnim.t0) / 700);
    const e = 1 - Math.pow(1 - k, 3);
    for (const m of spreadGroup.children) {
      const s = m.userData.slot;
      if (!s) continue; // 가운데 빈 파일은 고정
      m.position.x = s.x * e;
      m.position.y = s.y * e;
      m.rotation.z = THREE.MathUtils.degToRad(s.r) * e;
    }
    if (k >= 1) spreadAnim = null;
  }
  // 겹치기: 어느 쪽에서 보든 그림이 거울상이 되지 않게 자동 보정
  if (overlay?.mesh) {
    const below = camera.position.z < overlay.mesh.position.z;
    const sx = overlay.scale * (below ? -1 : 1);
    if (overlay.mesh.scale.x !== sx) overlay.mesh.scale.x = sx;
  }
  controls.update();
  renderer.render(scene, camera);
}
animate();
