(function () {
"use strict";

/* ============================ utilities ============================ */
const $ = (id) => document.getElementById(id);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const reduceMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;
const tok = (n) => getComputedStyle(document.documentElement).getPropertyValue(n).trim() || "#888";
function hexRgb(h) {
  h = h.replace("#", "");
  if (h.length === 3) h = h.split("").map((c) => c + c).join("");
  const n = parseInt(h, 16);
  return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}
function mix(a, b, t) { return [0, 1, 2].map((i) => Math.round(a[i] + (b[i] - a[i]) * t)); }
const rgba = (c, a) => `rgba(${c[0]},${c[1]},${c[2]},${a})`;
const SUP = { "-": "⁻", "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹" };
function fmt(v, sig = 3) {
  if (!isFinite(v)) return "—";
  if (v === 0) return "0";
  const a = Math.abs(v);
  if (a < 1e-3 || a >= 1e5) {
    const e = Math.floor(Math.log10(a)), m = v / Math.pow(10, e);
    return m.toFixed(2) + "·10" + String(e).split("").map((c) => SUP[c]).join("");
  }
  if (a >= 100) return v.toFixed(0);
  return Number(v.toPrecision(sig)).toString();
}
function fmtC(re, im) {
  if (Math.abs(im) < 1e-9) return fmt(re);
  const r = Math.abs(re) < 1e-9 ? "" : fmt(re) + " ";
  return r + (im < 0 ? "− " : (r ? "+ " : "")) + fmt(Math.abs(im)) + "i";
}
function setupCanvas(cv) {
  const r = cv.getBoundingClientRect(), d = window.devicePixelRatio || 1;
  const w = Math.max(20, r.width), h = Math.max(20, r.height);
  const W = Math.round(w * d), H = Math.round(h * d);
  if (cv.width !== W || cv.height !== H) { cv.width = W; cv.height = H; }
  const ctx = cv.getContext("2d");
  ctx.setTransform(d, 0, 0, d, 0, 0);
  return { ctx, w, h };
}
function niceTicks(a, b, n = 5) {
  const span = b - a; if (span <= 0) return [a];
  const step0 = span / n, mag = Math.pow(10, Math.floor(Math.log10(step0)));
  const f = step0 / mag, step = (f < 1.5 ? 1 : f < 3 ? 2 : f < 7 ? 5 : 10) * mag;
  const out = []; for (let v = Math.ceil(a / step) * step; v <= b + step * 1e-6; v += step) out.push(+v.toPrecision(10));
  return out;
}
function tickLabel(v) {
  const a = Math.abs(v);
  if (a !== 0 && (a < 1e-2 || a >= 1e5)) return fmt(v);
  return String(+v.toPrecision(6));
}

/* registry: redraw on theme / resize, animate visible components */
const comps = [];
function register(c) { comps.push(c); return c; }
function redrawAll() { comps.forEach((c) => c.draw && c.draw()); }
let rT; addEventListener("resize", () => { clearTimeout(rT); rT = setTimeout(redrawAll, 80); });
new MutationObserver(redrawAll).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", redrawAll);
const vis = new Map();
const io = new IntersectionObserver((es) => es.forEach((e) => vis.set(e.target, e.isIntersecting)), { rootMargin: "100px" });
let last = performance.now();
function loop(now) {
  const dt = Math.min(0.05, (now - last) / 1000); last = now;
  comps.forEach((c) => { if (c.tick && c.el && vis.get(c.el)) c.tick(dt); });
  requestAnimationFrame(loop);
}

/* ============================ numerics ============================ */
// integrate x' = x ∘ g(x) in log coordinates (populations stay positive)
function simLog(g, x0, dt, steps, every = 1, stop) {
  const n = x0.length;
  let u = x0.map((v) => Math.log(Math.max(v, 1e-300)));
  const ex = (u) => u.map(Math.exp);
  const add = (u, k, h) => u.map((v, i) => v + h * k[i]);
  const T = [0], X = [x0.slice()];
  for (let s = 1; s <= steps; s++) {
    const k1 = g(ex(u)), k2 = g(ex(add(u, k1, dt / 2))), k3 = g(ex(add(u, k2, dt / 2))), k4 = g(ex(add(u, k3, dt)));
    for (let i = 0; i < n; i++) u[i] += dt / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]);
    if (s % every === 0) {
      const x = ex(u); T.push(s * dt); X.push(x);
      if (stop && stop(x, s * dt)) break;
    }
  }
  return { T, X };
}
function simLin(A, p, dt, steps, bound) {
  const f = (x, y) => [A[0] * x + A[1] * y, A[2] * x + A[3] * y];
  const pts = [p.slice()]; let [x, y] = p;
  for (let s = 0; s < steps; s++) {
    const k1 = f(x, y), k2 = f(x + dt / 2 * k1[0], y + dt / 2 * k1[1]), k3 = f(x + dt / 2 * k2[0], y + dt / 2 * k2[1]), k4 = f(x + dt * k3[0], y + dt * k3[1]);
    x += dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]); y += dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]);
    pts.push([x, y]);
    if (Math.abs(x) > bound || Math.abs(y) > bound || (Math.abs(x) < 1e-4 && Math.abs(y) < 1e-4)) break;
  }
  return pts;
}
function bisect(f, a, b, it = 200) {
  let fa = f(a);
  for (let i = 0; i < it; i++) { const m = (a + b) / 2, fm = f(m); if ((fm > 0) === (fa > 0)) { a = m; fa = fm; } else b = m; }
  return (a + b) / 2;
}
// eigenvalues of small real matrix: Faddeev–LeVerrier + Durand–Kerner
function eig(M) {
  const n = M.length;
  if (n === 1) return [[M[0][0], 0]];
  const mul = (A, B) => A.map((r, i) => B[0].map((_, j) => r.reduce((s, _, k) => s + A[i][k] * B[k][j], 0)));
  const I = M.map((r, i) => r.map((_, j) => (i === j ? 1 : 0)));
  let Mk = I.map((r) => r.slice()); const c = [1];
  for (let k = 1; k <= n; k++) {
    const AM = mul(M, Mk);
    const ck = -AM.reduce((s, r, i) => s + r[i], 0) / k; c.push(ck);
    Mk = AM.map((r, i) => r.map((v, j) => v + (i === j ? ck : 0)));
  }
  // roots of z^n + c1 z^(n-1) + ... + cn
  const cm = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
  const cd = (a, b) => { const d = b[0] * b[0] + b[1] * b[1] || 1e-300; return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; };
  const P = (z) => { let r = [1, 0]; for (let k = 1; k <= n; k++) { r = cm(r, z); r[0] += c[k]; } return r; };
  const scale = 1 + Math.max(...c.map(Math.abs));
  let z = Array.from({ length: n }, (_, k) => { const a = 2 * Math.PI * k / n + 0.4; return [scale * 0.6 * Math.cos(a), scale * 0.6 * Math.sin(a)]; });
  for (let it = 0; it < 500; it++) {
    let moved = 0;
    z = z.map((zi, i) => {
      let den = [1, 0]; z.forEach((zj, j) => { if (j !== i) den = cm(den, [zi[0] - zj[0], zi[1] - zj[1]]); });
      const d = cd(P(zi), den); moved = Math.max(moved, Math.abs(d[0]) + Math.abs(d[1]));
      return [zi[0] - d[0], zi[1] - d[1]];
    });
    if (moved < 1e-13) break;
  }
  return z.map((v) => [v[0], Math.abs(v[1]) < 1e-8 ? 0 : v[1]]).sort((a, b) => b[0] - a[0]);
}
function solveLin(A, b) {
  const n = b.length, M = A.map((r, i) => r.concat([b[i]]));
  for (let i = 0; i < n; i++) {
    let p = i; for (let r = i + 1; r < n; r++) if (Math.abs(M[r][i]) > Math.abs(M[p][i])) p = r;
    if (Math.abs(M[p][i]) < 1e-12) return null;
    [M[i], M[p]] = [M[p], M[i]];
    for (let r = 0; r < n; r++) if (r !== i) { const f = M[r][i] / M[i][i]; for (let c = i; c <= n; c++) M[r][c] -= f * M[i][c]; }
  }
  return M.map((r, i) => r[n] / r[i]);
}
function classify2(tr, det, offdiagZero) {
  const eps = 1e-6, disc = tr * tr - 4 * det;
  if (det < -eps) return { name: "Sella", kind: "bad", stab: "instabile" };
  if (Math.abs(det) <= eps) return { name: "Equilibri non isolati", kind: "warn", stab: "det A = 0" };
  if (disc < -eps) {
    if (Math.abs(tr) <= 0.02) return { name: "Centro", kind: "warn", stab: "stabile, non asintoticamente" };
    return tr < 0 ? { name: "Fuoco stabile", kind: "good", stab: "asintoticamente stabile" } : { name: "Fuoco instabile", kind: "bad", stab: "instabile" };
  }
  if (Math.abs(disc) <= 0.02) {
    const nm = offdiagZero ? "Nodo stellato" : "Nodo improprio";
    return tr < 0 ? { name: nm + " stabile", kind: "good", stab: "asintoticamente stabile" } : { name: nm + " instabile", kind: "bad", stab: "instabile" };
  }
  return tr < 0 ? { name: "Nodo stabile", kind: "good", stab: "asintoticamente stabile" } : { name: "Nodo instabile", kind: "bad", stab: "instabile" };
}
function setStatus(el, kind, title, sub) {
  el.className = "status " + (kind || "");
  el.innerHTML = `<b>${title}</b>${sub ? `<small>${sub}</small>` : ""}`;
}
function setRO(el, rows) { el.innerHTML = rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join(""); }

/* ============================ 2D plane ============================ */
class Plane {
  constructor(cv, o) {
    this.cv = cv; this.o = Object.assign({ x0: 0, x1: 1, y0: 0, y1: 1, log: false, xl: "x", yl: "y", m: [12, 14, 34, 48] }, o);
    this.ctx = null;
  }
  set(o) { Object.assign(this.o, o); }
  snapshot() { if (!this.off) this.off = document.createElement("canvas"); this.off.width = this.cv.width; this.off.height = this.cv.height; this.off.getContext("2d").drawImage(this.cv, 0, 0); }
  restore() { const c = this.ctx; c.save(); c.setTransform(1, 0, 0, 1, 0, 0); c.drawImage(this.off, 0, 0); c.restore(); }
  frame() {
    const { ctx, w, h } = setupCanvas(this.cv); this.ctx = ctx; this.w = w; this.h = h;
    const [mt, mr, mb, ml] = this.o.m; this.L = ml; this.R = w - mr; this.T = mt; this.B = h - mb;
    const o = this.o;
    if (o.log) { this.ax0 = Math.log10(o.x0); this.ax1 = Math.log10(o.x1); this.ay0 = Math.log10(o.y0); this.ay1 = Math.log10(o.y1); }
    else { this.ax0 = o.x0; this.ax1 = o.x1; this.ay0 = o.y0; this.ay1 = o.y1; }
    this.col = { paper: tok("--paper"), ink: tok("--ink"), muted: tok("--muted"), rule: tok("--rule"), grid: tok("--grid"), accent: tok("--accent"), soft: tok("--accent-soft"), red: tok("--red") };
    ctx.fillStyle = this.col.paper; ctx.fillRect(0, 0, w, h);
    return ctx;
  }
  tx(x) { const v = this.o.log ? Math.log10(Math.max(x, 1e-300)) : x; return this.L + (v - this.ax0) / (this.ax1 - this.ax0) * (this.R - this.L); }
  ty(y) { const v = this.o.log ? Math.log10(Math.max(y, 1e-300)) : y; return this.B - (v - this.ay0) / (this.ay1 - this.ay0) * (this.B - this.T); }
  ix(px) { const v = this.ax0 + (px - this.L) / (this.R - this.L) * (this.ax1 - this.ax0); return this.o.log ? Math.pow(10, v) : v; }
  iy(py) { const v = this.ay0 + (this.B - py) / (this.B - this.T) * (this.ay1 - this.ay0); return this.o.log ? Math.pow(10, v) : v; }
  clip() { const c = this.ctx; c.save(); c.beginPath(); c.rect(this.L, this.T, this.R - this.L, this.B - this.T); c.clip(); }
  unclip() { this.ctx.restore(); }
  axes() {
    const c = this.ctx, o = this.o;
    const ticks = (a0, a1) => {
      if (!o.log) return niceTicks(a0, a1, 5).map((v) => [v, v]);
      const out = []; for (let e = Math.ceil(a0); e <= Math.floor(a1); e++) out.push([e, Math.pow(10, e)]);
      if (out.length > 7) return out.filter((_, i) => i % Math.ceil(out.length / 6) === 0);
      return out;
    };
    c.font = "500 11px 'IBM Plex Mono', ui-monospace, monospace"; c.fillStyle = this.col.muted;
    c.textAlign = "center"; c.textBaseline = "top";
    ticks(this.ax0, this.ax1).forEach(([a, v]) => {
      const X = this.L + (a - this.ax0) / (this.ax1 - this.ax0) * (this.R - this.L);
      c.fillStyle = this.col.grid; c.fillRect(Math.round(X), this.T, 1, this.B - this.T);
      c.fillStyle = this.col.muted; c.fillText(o.log ? "10" + String(a).split("").map((ch) => SUP[ch]).join("") : tickLabel(v), X, this.B + 5);
    });
    c.textAlign = "right"; c.textBaseline = "middle";
    ticks(this.ay0, this.ay1).forEach(([a, v]) => {
      const Y = this.B - (a - this.ay0) / (this.ay1 - this.ay0) * (this.B - this.T);
      c.fillStyle = this.col.grid; c.fillRect(this.L, Math.round(Y), this.R - this.L, 1);
      c.fillStyle = this.col.muted; c.fillText(o.log ? "10" + String(a).split("").map((ch) => SUP[ch]).join("") : tickLabel(v), this.L - 6, Y);
    });
    c.strokeStyle = this.col.rule; c.lineWidth = 1; c.strokeRect(this.L + 0.5, this.T + 0.5, this.R - this.L - 1, this.B - this.T - 1);
    if (!o.log) {
      c.strokeStyle = this.col.muted; c.lineWidth = 1.2; c.beginPath();
      if (this.ax0 < 0 && this.ax1 > 0) { const X = this.tx(0); c.moveTo(X, this.T); c.lineTo(X, this.B); }
      if (this.ay0 < 0 && this.ay1 > 0) { const Y = this.ty(0); c.moveTo(this.L, Y); c.lineTo(this.R, Y); }
      c.stroke();
    }
    c.font = "600 12px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.fillStyle = this.o.xc || this.col.ink;
    c.textAlign = "right"; c.textBaseline = "bottom"; c.fillText(o.xl, this.R - 4, this.B - 4);
    c.save(); c.translate(this.L + 6, this.T + 4); c.rotate(-Math.PI / 2); c.textAlign = "right"; c.textBaseline = "top"; c.fillStyle = this.o.yc || this.col.ink; c.fillText(o.yl, 0, 0); c.restore();
  }
  heat(V, levels, hi) {
    // filled sublevel bands + contour lines of V (sampled in screen space, works with log axes)
    const c = this.ctx, nx = 96, ny = Math.round(96 * (this.B - this.T) / (this.R - this.L));
    const vals = new Float64Array((nx + 1) * (ny + 1));
    for (let j = 0; j <= ny; j++) for (let i = 0; i <= nx; i++) {
      const px = this.L + i / nx * (this.R - this.L), py = this.T + j / ny * (this.B - this.T);
      vals[j * (nx + 1) + i] = V(this.ix(px), this.iy(py));
    }
    const off = document.createElement("canvas"); off.width = nx; off.height = ny;
    const oc = off.getContext("2d"), img = oc.createImageData(nx, ny);
    const a = hexRgb(this.col.soft), b = hexRgb(this.col.paper), top = levels[levels.length - 1];
    for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
      const v = vals[j * (nx + 1) + i]; let band = levels.findIndex((L) => v <= L); if (band < 0) band = levels.length;
      const t = Math.min(1, band / levels.length) * 0.9 + (isFinite(v) ? 0 : 0.1);
      const col = mix(a, b, t), p = (j * nx + i) * 4;
      img.data[p] = col[0]; img.data[p + 1] = col[1]; img.data[p + 2] = col[2]; img.data[p + 3] = 255;
    }
    oc.putImageData(img, 0, 0);
    c.imageSmoothingEnabled = true; c.drawImage(off, this.L, this.T, this.R - this.L, this.B - this.T);
    // contour lines (marching squares)
    const dx = (this.R - this.L) / nx, dy = (this.B - this.T) / ny;
    levels.forEach((L) => {
      c.beginPath(); c.strokeStyle = rgba(hexRgb(this.col.accent), L === hi ? 0 : 0.28); c.lineWidth = 1;
      for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
        const v00 = vals[j * (nx + 1) + i], v10 = vals[j * (nx + 1) + i + 1], v01 = vals[(j + 1) * (nx + 1) + i], v11 = vals[(j + 1) * (nx + 1) + i + 1];
        const e = []; const X = this.L + i * dx, Y = this.T + j * dy;
        const cr = (va, vb) => (L - va) / (vb - va);
        if ((v00 > L) !== (v10 > L)) e.push([X + cr(v00, v10) * dx, Y]);
        if ((v10 > L) !== (v11 > L)) e.push([X + dx, Y + cr(v10, v11) * dy]);
        if ((v01 > L) !== (v11 > L)) e.push([X + cr(v01, v11) * dx, Y + dy]);
        if ((v00 > L) !== (v01 > L)) e.push([X, Y + cr(v00, v01) * dy]);
        if (e.length >= 2) { c.moveTo(e[0][0], e[0][1]); c.lineTo(e[1][0], e[1][1]); if (e.length === 4) { c.moveTo(e[2][0], e[2][1]); c.lineTo(e[3][0], e[3][1]); } }
      }
      c.stroke();
    });
  }
  field(F, n = 22) {
    const c = this.ctx, ny = Math.max(8, Math.round(n * (this.B - this.T) / (this.R - this.L)));
    const sx = (this.R - this.L) / n, sy = (this.B - this.T) / ny, len = Math.min(sx, sy) * 0.42;
    const ink = hexRgb(this.col.muted);
    const items = []; let maxm = 0;
    for (let j = 0; j < ny; j++) for (let i = 0; i < n; i++) {
      const px = this.L + (i + 0.5) * sx, py = this.T + (j + 0.5) * sy, x = this.ix(px), y = this.iy(py);
      const v = F(x, y); if (!v) continue;
      // direction in screen space (finite difference of mapping)
      const h = 1e-4 * (1 + Math.abs(x) + Math.abs(y));
      const X2 = this.tx(x + v[0] * h), Y2 = this.ty(y + v[1] * h);
      let ux = X2 - px, uy = Y2 - py; const m = Math.hypot(ux, uy); if (!(m > 0)) continue;
      const mag = Math.hypot(v[0], v[1]); maxm = Math.max(maxm, mag);
      items.push([px, py, ux / m, uy / m, mag]);
    }
    c.lineWidth = 1.1; c.lineCap = "round";
    items.forEach(([px, py, ux, uy, mag]) => {
      const a = 0.22 + 0.45 * Math.min(1, Math.log1p(mag) / Math.log1p(maxm || 1));
      c.strokeStyle = rgba(ink, a); c.fillStyle = rgba(ink, a);
      const x0 = px - ux * len / 2, y0 = py - uy * len / 2, x1 = px + ux * len / 2, y1 = py + uy * len / 2;
      c.beginPath(); c.moveTo(x0, y0); c.lineTo(x1, y1); c.stroke();
      c.beginPath(); c.moveTo(x1, y1); c.lineTo(x1 - ux * 4 - uy * 2.6, y1 - uy * 4 + ux * 2.6); c.lineTo(x1 - ux * 4 + uy * 2.6, y1 - uy * 4 - ux * 2.6); c.closePath(); c.fill();
    });
  }
  path(pts, color, w = 2, alpha = 1, dash) {
    const c = this.ctx; if (!pts.length) return;
    c.strokeStyle = color; c.globalAlpha = alpha; c.lineWidth = w; c.lineJoin = "round"; c.setLineDash(dash || []);
    c.beginPath(); pts.forEach((p, i) => { const X = this.tx(p[0]), Y = this.ty(p[1]); i ? c.lineTo(X, Y) : c.moveTo(X, Y); }); c.stroke();
    c.globalAlpha = 1; c.setLineDash([]);
  }
  dot(x, y, r, fill, stroke, label, lc) {
    const c = this.ctx, X = this.tx(x), Y = this.ty(y);
    c.beginPath(); c.arc(X, Y, r, 0, 7); c.fillStyle = fill; c.fill();
    if (stroke) { c.lineWidth = 2; c.strokeStyle = stroke; c.stroke(); }
    if (label) {
      c.font = "600 12px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.fillStyle = lc || this.col.ink;
      const right = X > this.R - 70; c.textAlign = right ? "right" : "left"; c.textBaseline = "bottom";
      c.fillText(label, X + (right ? -8 : 8), Y - 5);
    }
  }
  onPick(cb) {
    this.cv.addEventListener("pointerdown", (e) => {
      const r = this.cv.getBoundingClientRect(), px = e.clientX - r.left, py = e.clientY - r.top;
      if (px < this.L || px > this.R || py < this.T || py > this.B) return;
      cb(this.ix(px), this.iy(py));
    });
  }
}

/* ============================ time series ============================ */
class TS {
  constructor(cv) { this.cv = cv; }
  draw(T, series, opt = {}) {
    const { ctx: c, w, h } = setupCanvas(this.cv);
    const m = [10, 12, 26, 48], L = m[3], R = w - m[1], Tp = m[0], B = h - m[2];
    c.fillStyle = tok("--paper"); c.fillRect(0, 0, w, h);
    if (!T || !T.length) return;
    const t0 = T[0], t1 = T[T.length - 1];
    let ymax = 0, ymin = 0; series.forEach((s) => s.y.forEach((v) => { if (isFinite(v)) { ymax = Math.max(ymax, v); ymin = Math.min(ymin, v); } }));
    if (!opt.signed) ymin = 0;
    const pad = (ymax - ymin) * 0.08 || 1; ymax += pad; if (ymin < 0) ymin -= pad;
    const X = (t) => L + (t - t0) / (t1 - t0 || 1) * (R - L), Y = (v) => B - (v - ymin) / (ymax - ymin) * (B - Tp);
    c.font = "500 11px 'IBM Plex Mono', ui-monospace, monospace";
    c.textAlign = "right"; c.textBaseline = "middle";
    niceTicks(ymin, ymax, 3).forEach((v) => { c.fillStyle = tok("--grid"); c.fillRect(L, Math.round(Y(v)), R - L, 1); c.fillStyle = tok("--muted"); c.fillText(tickLabel(v), L - 6, Y(v)); });
    c.textAlign = "center"; c.textBaseline = "top";
    niceTicks(t0, t1, 6).forEach((t) => { c.fillStyle = tok("--muted"); c.fillText(tickLabel(t), X(t), B + 5); });
    c.textAlign = "right"; c.textBaseline = "bottom"; c.fillText("t", R, B - 2);
    c.strokeStyle = tok("--rule"); c.strokeRect(L + 0.5, Tp + 0.5, R - L - 1, B - Tp - 1);
    // decimate for speed
    const step = Math.max(1, Math.floor(T.length / (R - L) / 1.5));
    series.forEach((s) => {
      c.strokeStyle = s.color; c.lineWidth = s.w || 1.8; c.globalAlpha = s.alpha || 1; c.setLineDash(s.dash || []);
      c.beginPath(); for (let i = 0; i < T.length; i += step) { const xx = X(T[i]), yy = Y(s.y[i]); i ? c.lineTo(xx, yy) : c.moveTo(xx, yy); } c.stroke();
      c.globalAlpha = 1; c.setLineDash([]);
    });
    if (opt.cursor != null) { c.fillStyle = tok("--ink"); c.globalAlpha = 0.35; c.fillRect(Math.round(X(opt.cursor)), Tp, 1, B - Tp); c.globalAlpha = 1; }
    // legend
    c.font = "600 11px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.textAlign = "left"; c.textBaseline = "middle";
    let lx = L + 8; series.filter((s) => s.label).forEach((s) => { c.fillStyle = s.color; c.fillRect(lx, Tp + 10, 12, 3); c.fillText(s.label, lx + 16, Tp + 11); lx += c.measureText(s.label).width + 30; });
  }
}

/* ============================ 3D view ============================ */
class View3D {
  constructor(cv, o = {}) {
    this.cv = cv; this.yaw = o.yaw ?? -0.75; this.pitch = o.pitch ?? 0.42; this.zoom = 1; this.auto = false; this.onchange = null;
    let drag = null; const pts = new Map();
    cv.addEventListener("pointerdown", (e) => { cv.setPointerCapture(e.pointerId); pts.set(e.pointerId, [e.clientX, e.clientY]); drag = [e.clientX, e.clientY, this.yaw, this.pitch]; });
    cv.addEventListener("pointermove", (e) => {
      if (!pts.has(e.pointerId)) return;
      const prev = pts.get(e.pointerId); pts.set(e.pointerId, [e.clientX, e.clientY]);
      if (pts.size === 2) {
        const [a, b] = [...pts.values()]; const d1 = Math.hypot(a[0] - b[0], a[1] - b[1]);
        const others = [...pts.entries()].filter(([k]) => k !== e.pointerId)[0][1];
        const d0 = Math.hypot(prev[0] - others[0], prev[1] - others[1]);
        if (d0 > 0) this.zoom = clamp(this.zoom * d1 / d0, 0.5, 3);
      } else if (drag) {
        this.yaw = drag[2] + (e.clientX - drag[0]) * 0.01; this.pitch = clamp(drag[3] + (e.clientY - drag[1]) * 0.008, -1.45, 1.45);
      }
      this.draw && this.draw();
    });
    const up = (e) => { pts.delete(e.pointerId); if (!pts.size) drag = null; };
    cv.addEventListener("pointerup", up); cv.addEventListener("pointercancel", up);
    cv.addEventListener("wheel", (e) => { e.preventDefault(); this.zoom = clamp(this.zoom * Math.exp(-e.deltaY * 0.0015), 0.5, 3); this.draw && this.draw(); }, { passive: false });
  }
  begin() {
    const { ctx, w, h } = setupCanvas(this.cv); this.ctx = ctx; this.w = w; this.h = h;
    ctx.fillStyle = tok("--paper"); ctx.fillRect(0, 0, w, h);
    const cy = Math.cos(this.yaw), sy = Math.sin(this.yaw), cp = Math.cos(this.pitch), sp = Math.sin(this.pitch);
    this.R = [cy, sy, cp, sp]; this.S = Math.min(w, h) * 0.31 * this.zoom; this.cx = w / 2; this.cyy = h / 2 + h * 0.03;
  }
  P(p) { // p in [-1,1]^3 (x, y, z-up)
    const [cy, sy, cp, sp] = this.R;
    const x1 = cy * p[0] - sy * p[1], y1 = sy * p[0] + cy * p[1];
    const y2 = cp * y1 - sp * p[2], z2 = sp * y1 + cp * p[2];
    return [this.cx + x1 * this.S, this.cyy - z2 * this.S, -y2];
  }
  box(ranges, labels, colors) {
    const c = this.ctx, mu = tok("--muted"), rule = tok("--rule");
    const corners = []; for (const x of [-1, 1]) for (const y of [-1, 1]) for (const z of [-1, 1]) corners.push([x, y, z]);
    const edges = [];
    for (let i = 0; i < 8; i++) for (let j = i + 1; j < 8; j++) { const d = corners[i].reduce((s, v, k) => s + (v !== corners[j][k]), 0); if (d === 1) edges.push([corners[i], corners[j]]); }
    // back faces grid: floor z=-1
    c.lineWidth = 1;
    c.strokeStyle = tok("--grid");
    for (let k = -1; k <= 1; k += 0.5) {
      const a = this.P([k, -1, -1]), b = this.P([k, 1, -1]), d = this.P([-1, k, -1]), e = this.P([1, k, -1]);
      c.beginPath(); c.moveTo(a[0], a[1]); c.lineTo(b[0], b[1]); c.moveTo(d[0], d[1]); c.lineTo(e[0], e[1]); c.stroke();
    }
    c.strokeStyle = rule;
    edges.forEach(([a, b]) => { const A = this.P(a), B = this.P(b); c.beginPath(); c.moveTo(A[0], A[1]); c.lineTo(B[0], B[1]); c.stroke(); });
    // axis ticks along three edges: choose edges nearest viewer at bottom
    c.font = "500 10.5px 'IBM Plex Mono', ui-monospace, monospace"; c.fillStyle = mu;
    const bc = this.P([0, 0, -1]);
    const pick = (ax) => {
      const o = [0, 1, 2].filter((k) => k !== ax); let best = null;
      for (const s1 of [-1, 1]) for (const s2 of [-1, 1]) {
        const a = [0, 0, 0], b = [0, 0, 0]; a[ax] = -1; b[ax] = 1; a[o[0]] = b[o[0]] = s1; a[o[1]] = b[o[1]] = s2;
        if (ax !== 2 && a[2] !== -1) continue;
        const A = this.P(a), B = this.P(b);
        const score = ax === 2 ? -(A[0] + B[0]) : A[2] + B[2];
        if (!best || score > best.s) best = { a, b, s: score };
      }
      return best;
    };
    [0, 1, 2].forEach((ax) => {
      const e = pick(ax), [lo, hi] = ranges[ax];
      c.font = "500 10.5px 'IBM Plex Mono', ui-monospace, monospace"; c.fillStyle = mu;
      niceTicks(lo, hi, 4).forEach((v) => {
        const t = (v - lo) / (hi - lo) * 2 - 1; const p = e.a.slice(); p[ax] = t; const q = this.P(p);
        if (ax === 2) { if (v <= lo) return; c.textAlign = "right"; c.textBaseline = "middle"; c.fillText(tickLabel(v), q[0] - 8, q[1]); return; }
        const dx = q[0] - bc[0], dy = q[1] - bc[1], m = Math.hypot(dx, dy) || 1;
        c.textAlign = Math.abs(dx / m) < 0.3 ? "center" : dx > 0 ? "left" : "right"; c.textBaseline = dy > 0 ? "top" : "bottom";
        c.fillText(tickLabel(v), q[0] + dx / m * 7, q[1] + dy / m * 7);
      });
      c.font = "600 12px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.fillStyle = (colors && colors[ax]) || tok("--ink");
      if (ax === 2) { const q = this.P(e.b); c.textAlign = "center"; c.textBaseline = "bottom"; c.fillText(labels[ax], q[0], q[1] - 10); return; }
      const mid = e.a.slice(); mid[ax] = 0; const q = this.P(mid), dx = q[0] - bc[0], dy = q[1] - bc[1], m = Math.hypot(dx, dy) || 1;
      c.textAlign = Math.abs(dx / m) < 0.3 ? "center" : dx > 0 ? "left" : "right"; c.textBaseline = dy > 0 ? "top" : "bottom";
      c.fillText(labels[ax], q[0] + dx / m * 30, q[1] + dy / m * 26);
    });
  }
  render(items) {
    const c = this.ctx;
    items.forEach((it) => { it.d = it.pts.reduce((s, p) => s + this.P(p)[2], 0) / it.pts.length + (it.bias || 0); });
    items.sort((a, b) => a.d - b.d);
    items.forEach((it) => {
      const q = it.pts.map((p) => this.P(p));
      if (it.t === "quad") {
        c.beginPath(); q.forEach((p, i) => (i ? c.lineTo(p[0], p[1]) : c.moveTo(p[0], p[1]))); c.closePath();
        c.fillStyle = it.fill; c.fill(); if (it.stroke) { c.strokeStyle = it.stroke; c.lineWidth = 0.6; c.stroke(); }
      } else if (it.t === "seg") {
        c.strokeStyle = it.color; c.lineWidth = it.w || 2; c.lineCap = "round"; c.globalAlpha = it.a ?? 1;
        c.beginPath(); c.moveTo(q[0][0], q[0][1]); c.lineTo(q[1][0], q[1][1]); c.stroke(); c.globalAlpha = 1;
      } else if (it.t === "dot") {
        c.beginPath(); c.arc(q[0][0], q[0][1], it.r || 4, 0, 7); c.fillStyle = it.color; c.fill();
        if (it.ring) { c.strokeStyle = it.ring; c.lineWidth = 2; c.stroke(); }
        if (it.label) { c.font = "600 11px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.fillStyle = it.lc || tok("--ink"); c.textAlign = "left"; c.textBaseline = "bottom"; c.fillText(it.label, q[0][0] + 7, q[0][1] - 4); }
      }
    });
  }
}

/* ============================ 1. linear systems ============================ */
(function linear() {
  const cv = $("lin-cv"), tdcv = $("lin-td"); if (!cv) return;
  const ids = ["a", "b", "c", "d"], sl = ids.map((k) => $("lin-" + k));
  const PRE = [
    ["Nodo stabile", [-2, 0.5, 0.3, -1]], ["Nodo instabile", [1.5, 0.4, 0.2, 0.8]], ["Sella", [1, 0.5, 0.8, -1]],
    ["Fuoco stabile", [-0.3, -1.5, 1.5, -0.3]], ["Fuoco instabile", [0.25, 1.4, -1.4, 0.25]], ["Centro", [0, -1.5, 1.5, 0]],
    ["Nodo stellato", [-1, 0, 0, -1]], ["Nodo improprio", [-1, 1, 0, -1]],
  ];
  const presetBox = $("lin-presets");
  PRE.forEach(([n, A]) => { const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = n; b.onclick = () => { setA(A); }; presetBox.appendChild(b); });
  let A = PRE[3][1].slice(), user = [], parts = [];
  const LEAVES = [
    { g: "c", id: "ciclo", name: "Ciclo", cond: "α = 0", A: [0, -1.5, 1.5, 0] },
    { g: "c", id: "fs+", name: "Fuoco stabile", cond: "α < 0, β > 0", A: [-0.3, 1.5, -1.5, -0.3] },
    { g: "c", id: "fs-", name: "Fuoco stabile", cond: "α < 0, β < 0", A: [-0.3, -1.5, 1.5, -0.3] },
    { g: "c", id: "fi+", name: "Fuoco instabile", cond: "α > 0, β > 0", A: [0.25, 1.4, -1.4, 0.25] },
    { g: "c", id: "fi-", name: "Fuoco instabile", cond: "α > 0, β < 0", A: [0.25, -1.4, 1.4, 0.25] },
    { g: "eqd", id: "nsi", name: "Nodo stellato instabile", cond: "λ > 0", A: [1, 0, 0, 1] },
    { g: "eqd", id: "nss", name: "Nodo stellato stabile", cond: "λ < 0", A: [-1, 0, 0, -1] },
    { g: "eqn", id: "nii", name: "Nodo improprio instabile", cond: "λ > 0", A: [1, 1, 0, 1] },
    { g: "eqn", id: "nis", name: "Nodo improprio stabile", cond: "λ < 0", A: [-1, 1, 0, -1] },
    { g: "ne", id: "ns", name: "Nodo stabile", cond: "λ₁ < 0, λ₂ < 0", A: [-2, 0, 0, -0.8] },
    { g: "ne", id: "s1", name: "Sella", cond: "λ₁ < 0, λ₂ > 0", A: [-1, 0, 0, 1.2] },
    { g: "ne", id: "s2", name: "Sella", cond: "λ₁ > 0, λ₂ < 0", A: [1.2, 0, 0, -1] },
    { g: "ne", id: "ni", name: "Nodo instabile", cond: "λ₁ > 0, λ₂ > 0", A: [1.5, 0, 0, 0.7] },
  ];
  const treeEl = $("lin-tree");
  if (treeEl) {
    const grp = (g) => LEAVES.filter((l) => l.g === g).map((l) => `<button type="button" class="leaf" data-leaf="${l.id}"><canvas width="64" height="64" aria-hidden="true"></canvas><span class="leaf-t">${l.name}</span><span class="leaf-c">${l.cond}</span></button>`).join("");
    treeEl.innerHTML = `<div class="t-root"><span class="node">A: λ₁, λ₂</span></div>
      <div class="t-cols">
        <div class="t-col"><span class="node">λ₁, λ₂ ∈ ℂ</span><div class="leaves">${grp("c")}</div></div>
        <div class="t-col"><span class="node">λ₁, λ₂ ∈ ℝ, λ₁ = λ₂ = λ</span><div class="t-sub"><span class="node sm">A diagonalizzabile</span><div class="leaves">${grp("eqd")}</div></div><div class="t-sub"><span class="node sm">A non diagonalizzabile</span><div class="leaves">${grp("eqn")}</div></div></div>
        <div class="t-col"><span class="node">λ₁, λ₂ ∈ ℝ, λ₁ ≠ λ₂</span><div class="leaves">${grp("ne")}</div></div>
      </div>`;
    treeEl.querySelectorAll(".leaf").forEach((b) => { const l = LEAVES.find((q) => q.id === b.dataset.leaf); b.onclick = () => setA(l.A); });
  }
  function drawLeaves() {
    if (!treeEl) return;
    treeEl.querySelectorAll(".leaf").forEach((b) => {
      const l = LEAVES.find((q) => q.id === b.dataset.leaf), cv2 = b.querySelector("canvas"), { ctx: c, w, h } = setupCanvas(cv2);
      c.fillStyle = tok("--paper"); c.fillRect(0, 0, w, h);
      c.strokeStyle = tok("--rule"); c.lineWidth = 1; c.beginPath(); c.moveTo(w / 2, 0); c.lineTo(w / 2, h); c.moveTo(0, h / 2); c.lineTo(w, h / 2); c.stroke();
      const M = l.A, s = w / 6.4;
      const seeds = []; for (let k = 0; k < 8; k++) { const a = k / 8 * 2 * Math.PI + 0.25; seeds.push([2.6 * Math.cos(a), 2.6 * Math.sin(a)]); }
      for (let k = 0; k < 6; k++) { const a = k / 6 * 2 * Math.PI + 0.5; seeds.push([0.15 * Math.cos(a), 0.15 * Math.sin(a)]); }
      c.strokeStyle = tok("--red"); c.lineWidth = 1;
      seeds.forEach((p) => { const pts = simLin(M, p, 0.03, 350, 6); c.beginPath(); pts.forEach((q, i) => { const X = w / 2 + q[0] * s, Y = h / 2 - q[1] * s; i ? c.lineTo(X, Y) : c.moveTo(X, Y); }); c.stroke(); });
    });
  }
  function leafOf() {
    const tr = A[0] + A[3], det = A[0] * A[3] - A[1] * A[2], disc = tr * tr - 4 * det, e = 1e-6;
    if (det < -e) {
      // which eigenvector of the negative eigenvalue is closer to the x axis?
      const l = (tr - Math.sqrt(disc)) / 2; let v = Math.abs(A[1]) > 1e-9 ? [A[1], l - A[0]] : Math.abs(A[2]) > 1e-9 ? [l - A[3], A[2]] : (Math.abs(A[0] - l) < 1e-9 ? [1, 0] : [0, 1]);
      return Math.abs(v[0]) >= Math.abs(v[1]) ? "s1" : "s2";
    }
    if (Math.abs(det) <= e) return null;
    if (disc < -e) { if (Math.abs(tr) <= 0.02) return "ciclo"; const beta = A[2] < 0 ? "+" : "-"; return (tr < 0 ? "fs" : "fi") + beta; }
    if (Math.abs(disc) <= 0.02) { const diag = Math.abs(A[1]) < 1e-9 && Math.abs(A[2]) < 1e-9; return diag ? (tr < 0 ? "nss" : "nsi") : (tr < 0 ? "nis" : "nii"); }
    return tr < 0 ? "ns" : "ni";
  }
  const plane = new Plane(cv, { x0: -3, x1: 3, y0: -3, y1: 3, xl: "x", yl: "y" });
  const td = { cv: tdcv };
  function setA(a) { A = a.slice(); sl.forEach((s, i) => (s.value = A[i])); user = []; update(); }
  sl.forEach((s, i) => s.addEventListener("input", () => { A[i] = +s.value; update(); }));
  let trajs = [];
  function compute() {
    trajs = [];
    for (let k = 0; k < 10; k++) { const a = k / 10 * 2 * Math.PI + 0.2; trajs.push({ pts: simLin(A, [2.9 * Math.cos(a), 2.9 * Math.sin(a)], 0.02, 700, 6) }); }
    for (let k = 0; k < 6; k++) { const a = k / 6 * 2 * Math.PI + 0.5; trajs.push({ pts: simLin(A, [0.12 * Math.cos(a), 0.12 * Math.sin(a)], 0.02, 700, 6) }); }
    user.forEach((p) => { const f = simLin(A, p, 0.02, 900, 40), b = simLin(A.map((v) => -v), p, 0.02, 900, 40); trajs.push({ pts: b.reverse().concat(f.slice(1)), user: true }); });
  }
  function info() {
    const tr = A[0] + A[3], det = A[0] * A[3] - A[1] * A[2], disc = tr * tr - 4 * det;
    let l1, l2; if (disc >= 0) { l1 = [(tr + Math.sqrt(disc)) / 2, 0]; l2 = [(tr - Math.sqrt(disc)) / 2, 0]; } else { l1 = [tr / 2, Math.sqrt(-disc) / 2]; l2 = [tr / 2, -Math.sqrt(-disc) / 2]; }
    return { tr, det, disc, l1, l2, cls: classify2(tr, det, Math.abs(A[1]) < 1e-9 && Math.abs(A[2]) < 1e-9) };
  }
  // flow particles
  let parts0 = () => Array.from({ length: 70 }, () => ({ x: (Math.random() * 2 - 1) * 3, y: (Math.random() * 2 - 1) * 3, life: Math.random() * 4 }));
  parts = parts0();
  function draw() {
    const c = plane.frame(); plane.clip();
    plane.field((x, y) => [A[0] * x + A[1] * y, A[2] * x + A[3] * y], 20);
    staticPart(c);
    plane.unclip(); plane.axes(); plane.snapshot();
    particles();
    drawTD(info());
  }
  function particles() {
    const c = plane.ctx, ink = hexRgb(tok("--ink"));
    plane.clip();
    parts.forEach((p) => { c.fillStyle = rgba(ink, 0.6 * Math.min(1, p.life, 4 - p.life + 0.2)); c.beginPath(); c.arc(plane.tx(p.x), plane.ty(p.y), 1.9, 0, 7); c.fill(); });
    plane.unclip();
  }
  function staticPart(c) {
    const I = info();
    if (I.disc > 1e-9 && Math.abs(I.det) > 1e-6) {
      [I.l1[0], I.l2[0]].forEach((l) => {
        // eigenvector of A for eigenvalue l
        let v = Math.abs(A[1]) > 1e-9 ? [A[1], l - A[0]] : Math.abs(A[2]) > 1e-9 ? [l - A[3], A[2]] : (Math.abs(A[0] - l) < 1e-9 ? [1, 0] : [0, 1]);
        const m = Math.hypot(v[0], v[1]); v = [v[0] / m * 10, v[1] / m * 10];
        plane.path([[-v[0], -v[1]], [v[0], v[1]]], l < 0 ? tok("--sp1") : tok("--sp2"), 1.4, 0.8, [6, 5]);
      });
    }
    trajs.forEach((t) => plane.path(t.pts, t.user ? tok("--red") : tok("--accent"), t.user ? 2.2 : 1.5, t.user ? 1 : 0.75));
    plane.dot(0, 0, 4.5, I.cls.kind === "good" ? tok("--good") : I.cls.kind === "bad" ? tok("--bad") : tok("--warn"), tok("--paper"));
  }
  // trace–determinant plane
  const TDR = 4;
  function tdMap() {
    const { ctx, w, h } = setupCanvas(tdcv); const m = 14;
    return { ctx, w, h, X: (t) => m + (t + TDR) / (2 * TDR) * (w - 2 * m), Y: (d) => h - m - (d + TDR * 0.7) / (TDR * 1.7) * (h - 2 * m), iX: (px) => (px - m) / (w - 2 * m) * 2 * TDR - TDR, iY: (py) => (h - m - py) / (h - 2 * m) * TDR * 1.7 - TDR * 0.7 };
  }
  function drawTD(I) {
    const M = tdMap(), c = M.ctx;
    c.fillStyle = tok("--paper"); c.fillRect(0, 0, M.w, M.h);
    // regions
    const good = hexRgb(tok("--good-bg")), bad = hexRgb(tok("--bad-bg"));
    c.fillStyle = rgba(bad, 1); c.fillRect(0, M.Y(0), M.w, M.h - M.Y(0));
    c.fillStyle = rgba(good, 1); c.fillRect(0, 0, M.X(0), M.Y(0));
    c.strokeStyle = tok("--muted"); c.lineWidth = 1;
    c.beginPath(); c.moveTo(M.X(-TDR), M.Y(0)); c.lineTo(M.X(TDR), M.Y(0)); c.moveTo(M.X(0), 0); c.lineTo(M.X(0), M.h); c.stroke();
    c.strokeStyle = tok("--accent"); c.lineWidth = 1.6; c.beginPath();
    for (let t = -TDR; t <= TDR; t += 0.05) { const X = M.X(t), Y = M.Y(t * t / 4); t === -TDR ? c.moveTo(X, Y) : c.lineTo(X, Y); } c.stroke();
    c.font = "600 10.5px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.fillStyle = tok("--muted"); c.textBaseline = "middle"; c.textAlign = "center";
    c.fillText("sella", M.X(0) + 30, M.Y(-1.8));
    c.fillText("fuoco stab.", M.X(-1.5), M.Y(2.9)); c.fillText("fuoco instab.", M.X(1.5), M.Y(2.9));
    c.fillText("nodo stab.", M.X(-3.1), M.Y(0.9)); c.fillText("nodo instab.", M.X(3.05), M.Y(0.9));
    c.font = "500 10px 'IBM Plex Mono', monospace"; c.textAlign = "right"; c.textBaseline = "bottom"; c.fillText("tr A", M.w - 4, M.Y(0) - 2);
    c.textAlign = "left"; c.textBaseline = "top"; c.fillText("det A", M.X(0) + 4, 4);
    const px = M.X(clamp(I.tr, -TDR, TDR)), py = M.Y(clamp(I.det, -TDR * 0.7, TDR));
    c.beginPath(); c.arc(px, py, 7, 0, 7); c.fillStyle = tok("--red"); c.fill(); c.lineWidth = 2; c.strokeStyle = tok("--paper"); c.stroke();
  }
  let tdDrag = false;
  const tdMove = (e) => {
    const r = tdcv.getBoundingClientRect(), M = tdMap();
    const tr = clamp(M.iX(e.clientX - r.left), -3.9, 3.9), det = clamp(M.iY(e.clientY - r.top), -2.7, 4);
    const q = tr * tr / 4 - det; let b, c;
    if (q >= 0) { b = Math.sqrt(q); c = Math.sqrt(q); } else { b = Math.sqrt(-q); c = -Math.sqrt(-q); }
    A = [tr / 2, b, c, tr / 2].map((v) => Math.round(v * 100) / 100); sl.forEach((s, i) => (s.value = A[i])); update(true);
  };
  tdcv.addEventListener("pointerdown", (e) => { tdDrag = true; tdcv.setPointerCapture(e.pointerId); tdMove(e); });
  tdcv.addEventListener("pointermove", (e) => tdDrag && tdMove(e));
  tdcv.addEventListener("pointerup", () => (tdDrag = false));
  plane.onPick((x, y) => { user.push([x, y]); if (user.length > 6) user.shift(); update(); });
  function update() {
    sl.forEach((s, i) => (s.nextElementSibling.value = (+A[i]).toFixed(2)));
    compute();
    const I = info();
    setStatus($("lin-status"), I.cls.kind, I.cls.name, I.cls.stab + (I.disc < -1e-6 ? (A[2] < 0 ? " · rotazione oraria (β > 0)" : " · rotazione antioraria (β < 0)") : ""));
    setRO($("lin-ro"), [["tr A", fmt(I.tr)], ["det A", fmt(I.det)], ["Δ = tr² − 4 det", fmt(I.disc)], ["λ₁", fmtC(...I.l1)], ["λ₂", fmtC(...I.l2)]]);
    presetBox.querySelectorAll(".chip").forEach((b, i) => b.setAttribute("aria-pressed", PRE[i][1].every((v, k) => Math.abs(v - A[k]) < 1e-9)));
    if (treeEl) { const lf = leafOf(); treeEl.querySelectorAll(".leaf").forEach((b) => b.classList.toggle("on", b.dataset.leaf === lf)); }
    draw();
  }
  register({ draw: drawLeaves });
  const comp = register({ el: cv, draw, tick(dt) {
    if (reduceMotion) return;
    parts.forEach((p) => {
      for (let k = 0; k < 3; k++) { const vx = A[0] * p.x + A[1] * p.y, vy = A[2] * p.x + A[3] * p.y; p.x += vx * dt / 3 * 0.8; p.y += vy * dt / 3 * 0.8; }
      p.life -= dt;
      if (p.life <= 0 || Math.abs(p.x) > 3.2 || Math.abs(p.y) > 3.2 || (Math.abs(p.x) < 0.02 && Math.abs(p.y) < 0.02)) { p.x = (Math.random() * 2 - 1) * 3; p.y = (Math.random() * 2 - 1) * 3; p.life = 2 + Math.random() * 3; }
    });
    if (!plane.off) return draw();
    plane.restore(); particles();
  } });
  io.observe(cv);
  setA(A);
})();

/* ============================ 2–3. Lotka–Volterra ============================ */
const LV = { al: 0.6, be: 0.012, ga: 0.5, de: 0.005, h: 0, x: 40, y: 50, listeners: [] };
LV.eff = () => ({ a: Math.max(1e-4, LV.al - LV.h), b: LV.be, g: LV.ga + LV.h, d: LV.de });
LV.V = (x, y) => { const { a, b, g, d } = LV.eff(); const x0 = g / d, y0 = a / b; return d * (x - x0) - g * Math.log(x / x0) + b * (y - y0) - a * Math.log(y / y0); };
LV.extremes = (k) => {
  const { a, b, g, d } = LV.eff(), x0 = g / d, y0 = a / b;
  // V(x, y0) = k  ->  f(s) = d e^s - g s - (k + d x0 - g ln x0) = 0 with s = ln x
  const fx = (s) => d * Math.exp(s) - g * s - (k + d * x0 - g * Math.log(x0));
  const fy = (s) => b * Math.exp(s) - a * s - (k + b * y0 - a * Math.log(y0));
  const s0x = Math.log(x0), s0y = Math.log(y0);
  if (k <= 0) return { xmin: x0, xmax: x0, ymin: y0, ymax: y0 };
  return {
    xmin: Math.exp(bisect(fx, s0x - 800, s0x)), xmax: Math.exp(bisect(fx, s0x + 60, s0x)),
    ymin: Math.exp(bisect(fy, s0y - 800, s0y)), ymax: Math.exp(bisect(fy, s0y + 60, s0y)),
  };
};
LV.sim = (x, y) => {
  const { a, b, g, d } = LV.eff(), x0 = g / d, y0 = a / b;
  const T0 = 2 * Math.PI / Math.sqrt(a * g);
  const E = LV.extremes(LV.Vat(x, y));
  const rate = Math.max(b * E.ymax, d * E.xmax, a, g);
  const dt = Math.min(0.05, T0 / 300, 0.12 / rate);
  const every = Math.max(1, Math.round(T0 / 400 / dt));
  // detect a full turn in log coordinates around the equilibrium
  let ang = 0, prev = Math.atan2(Math.log(y / y0), Math.log(x / x0)), period = null;
  const r = simLog((v) => [a - b * v[1], -g + d * v[0]], [x, y], dt, 3000000, every, (v, t) => {
    const th = Math.atan2(Math.log(v[1] / y0), Math.log(v[0] / x0)); let dth = th - prev; if (dth > Math.PI) dth -= 2 * Math.PI; if (dth < -Math.PI) dth += 2 * Math.PI;
    ang += dth; prev = th;
    if (period == null && Math.abs(ang) >= 2 * Math.PI) period = t;
    return period != null && t >= period * 3 - 1e-9 || t > 3000;
  });
  return { T: r.T, X: r.X, period, T0, x0, y0 };
};
LV.Vat = (x, y) => LV.V(x, y);
LV.emit = (src) => LV.listeners.forEach((f) => f(src));

(function lotka() {
  const cv = $("lv-cv"); if (!cv) return;
  const ts = new TS($("lv-ts"));
  const plane = new Plane(cv, { xl: "prede x", yl: "predatori y" });
  const keys = [["al", "lv-al", 2], ["be", "lv-be", 3], ["ga", "lv-ga", 2], ["de", "lv-de", 4], ["h", "lv-h", 2]];
  const PRE = {
    reg: ["Orbite chiuse (Fig. 4.4 – 4.5)", { al: 0.6, be: 0.012, ga: 0.5, de: 0.005, h: 0, x: 40, y: 50 }],
    near: ["Vicino all'equilibrio", { al: 0.6, be: 0.012, ga: 0.5, de: 0.005, h: 0, x: 112, y: 50 }],
    big: ["Orbita ampia", { al: 0.6, be: 0.012, ga: 0.5, de: 0.005, h: 0, x: 15, y: 20 }],
    crollo: ["Crollo delle popolazioni (Tab. 4.1)", { al: 0.5, be: 0.02, ga: 0.8, de: 0.01, h: 0, x: 3500, y: 25 }],
  };
  const box = $("lv-presets");
  Object.entries(PRE).forEach(([id, [n, p]]) => { const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = n; b.dataset.id = id; b.onclick = () => load(id); box.appendChild(b); });
  document.querySelectorAll("[data-lv-preset]").forEach((b) => b.addEventListener("click", () => { load(b.dataset.lvPreset); $("lab-lv").scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "center" }); }));
  let cur = "reg";
  function load(id) {
    Object.assign(LV, PRE[id][1]); cur = id;
    keys.forEach(([k, el]) => ($(el).value = LV[k]));
    if (id === "crollo") $("lv-log").checked = true; else if (id !== "crollo") $("lv-log").checked = false;
    update();
  }
  keys.forEach(([k, el, dp]) => $(el) && $(el).addEventListener("input", (e) => { LV[k] = +e.target.value; cur = null; update(); }));
  window.LVload = (p, log) => { Object.assign(LV, p); cur = null; keys.forEach(([k, el]) => { if ($(el)) $(el).value = LV[k]; }); $("lv-log").checked = !!log; update(); };
  ["lv-field", "lv-levels", "lv-log"].forEach((id) => $(id).addEventListener("change", () => { bounds(); draw(); }));
  plane.onPick((x, y) => { if (x > 0 && y > 0) { LV.x = x; LV.y = y; cur = null; update(); } });
  let S = null, head = 0;
  function bounds() {
    const { x0, y0 } = S, X = S.X;
    let xmax = x0 * 2.2, ymax = y0 * 2.2, xmin = Infinity, ymin = Infinity;
    X.forEach((v) => { xmax = Math.max(xmax, v[0]); ymax = Math.max(ymax, v[1]); xmin = Math.min(xmin, v[0]); ymin = Math.min(ymin, v[1]); });
    if ($("lv-log").checked) {
      const lx0 = Math.floor(Math.log10(Math.max(1e-300, Math.min(xmin, x0))) - 0.3), lx1 = Math.ceil(Math.log10(xmax) + 0.2);
      const ly0 = Math.floor(Math.log10(Math.max(1e-300, Math.min(ymin, y0))) - 0.3), ly1 = Math.ceil(Math.log10(ymax) + 0.2);
      plane.set({ log: true, x0: Math.pow(10, lx0), x1: Math.pow(10, lx1), y0: Math.pow(10, ly0), y1: Math.pow(10, ly1) });
    } else plane.set({ log: false, x0: 0, x1: xmax * 1.1, y0: 0, y1: ymax * 1.12 });
  }
  function update() {
    keys.forEach(([k, el, dp]) => { const o = $(el) && $(el).nextElementSibling; if (o && o.tagName === "OUTPUT") o.value = (+LV[k]).toFixed(dp); });
    box.querySelectorAll(".chip").forEach((b) => b.setAttribute("aria-pressed", b.dataset.id === cur));
    S = LV.sim(LV.x, LV.y); head = 0; bounds();
    const k = LV.V(LV.x, LV.y), E = LV.extremes(k), { a, g } = LV.eff();
    // time averages over one period
    let mx = 0, my = 0, n = 0;
    if (S.period) for (let i = 1; i < S.T.length && S.T[i] <= S.period + 1e-9; i++) { const h = S.T[i] - S.T[i - 1]; mx += (S.X[i][0] + S.X[i - 1][0]) / 2 * h; my += (S.X[i][1] + S.X[i - 1][1]) / 2 * h; n += h; }
    const lowest = Math.min(E.xmin, E.ymin);
    if (lowest < 1) setStatus($("lv-status"), "bad", "Crollo delle popolazioni", `${E.xmin < E.ymin ? "Le prede scendono" : "I predatori scendono"} a ${fmt(lowest)}: per il modello rinascono, in natura la specie sarebbe estinta.`);
    else if (k < 0.02 * (S.x0 * LV.eff().d + S.y0 * LV.eff().b)) setStatus($("lv-status"), "good", "Piccole oscillazioni", "Vicino all'equilibrio le orbite sono quasi ellissi e il periodo tende a 2π/√(αγ).");
    else setStatus($("lv-status"), "warn", "Orbita chiusa", "Le popolazioni si ripetono identiche a ogni ciclo, senza smorzarsi.");
    setRO($("lv-ro"), [
      ["equilibrio (γ/δ, α/β)", `(${fmt(S.x0)}, ${fmt(S.y0)})`], ["autovalori", `± ${fmt(Math.sqrt(a * g))} i`],
      ["periodo piccole osc.", fmt(S.T0)], ["periodo dell'orbita", S.period ? fmt(S.period) : "—"],
      ["k = V(x_in, y_in)", fmt(k)], ["prede min / max", `${fmt(E.xmin)} / ${fmt(E.xmax)}`], ["predatori min / max", `${fmt(E.ymin)} / ${fmt(E.ymax)}`],
      ["media su un periodo", n ? `(${fmt(mx / n)}, ${fmt(my / n)})` : "—"],
    ]);
    draw(); LV.emit("lv");
  }
  function draw() {
    if (!S) return;
    plane.set({ xc: tok("--sp1"), yc: tok("--sp2") });
    plane.frame(); plane.clip();
    const k = LV.V(LV.x, LV.y);
    if ($("lv-levels").checked) { const lv = [0.05, 0.15, 0.35, 0.7, 1.2, 2, 3.2, 5, 8].map((f) => f * Math.max(k, 1e-3)); plane.heat(LV.V, lv, null); }
    if ($("lv-field").checked) { const { a, b, g, d } = LV.eff(); plane.field((x, y) => [a * x - b * x * y, -g * y + d * x * y], 20); }
    const stop = S.period ? S.X.length * Math.min(1, S.period / S.T[S.T.length - 1]) : S.X.length;
    plane.path(S.X.slice(0, Math.ceil(stop) + 2), tok("--accent"), 2.4);
    plane.dot(S.x0, S.y0, 5, tok("--red"), tok("--paper"), "(γ/δ, α/β)");
    plane.dot(LV.x, LV.y, 4, tok("--paper"), tok("--accent"));
    plane.unclip(); plane.axes(); plane.snapshot();
    dyn();
  }
  function dyn() {
    plane.restore(); plane.clip();
    const i = Math.floor(head) % S.X.length, p = S.X[i];
    plane.path([[p[0], plane.o.log ? plane.o.y0 : 0], p], tok("--sp1"), 1.3, 0.8, [3, 3]);
    plane.path([[plane.o.log ? plane.o.x0 : 0, p[1]], p], tok("--sp2"), 1.3, 0.8, [3, 3]);
    plane.dot(p[0], p[1], 6.5, tok("--ink"), tok("--paper"));
    plane.unclip();
    ts.draw(S.T, [{ y: S.X.map((v) => v[0]), color: tok("--sp1"), label: "prede x" }, { y: S.X.map((v) => v[1]), color: tok("--sp2"), label: "predatori y" }], { cursor: S.T[i] });
  }
  register({ el: cv, draw, tick(dt) {
    if (!S || reduceMotion) return;
    const per = S.period || S.T[S.T.length - 1] / 3;
    const ptsPerPeriod = S.X.length * per / S.T[S.T.length - 1];
    head = (head + dt * ptsPerPeriod / 7) % S.X.length; if (plane.off) dyn(); else draw();
  } });
  io.observe(cv);
  load("reg");
})();

(function lyapunov() {
  const cv = $("v-cv"); if (!cv) return;
  const view = new View3D(cv, { yaw: -2.3, pitch: 0.38 });
  const mini = new Plane($("v-2d"), { xl: "x", yl: "y", m: [8, 8, 26, 40] });
  const ks = $("v-k");
  let K = null, orbit = [], dom = null;
  function domain() {
    const { a, b, g, d } = LV.eff(), x0 = g / d, y0 = a / b;
    const X = 3 * x0, Y = 3 * y0;
    const zcap = Math.max(LV.V(X, Y * 0.5), LV.V(X * 0.5, Y), LV.V(x0 * 0.1, y0), LV.V(x0, y0 * 0.1));
    dom = { x0, y0, X, Y, zcap };
  }
  function setKFromLV() {
    domain(); const k = LV.V(LV.x, LV.y);
    ks.max = (dom.zcap * 0.85).toPrecision(4); ks.step = (dom.zcap / 400).toPrecision(3);
    K = clamp(k, 0, +ks.max); ks.value = K; compute();
  }
  function compute() {
    ks.nextElementSibling.value = fmt(K);
    orbit = [];
    if (K > 1e-9) {
      // start on the ray y = y0, x > x0
      const { x0, y0 } = dom, { a, b, g, d } = LV.eff();
      const xs = Math.exp(bisect((s) => LV.V(Math.exp(s), y0) - K, Math.log(x0) + 60, Math.log(x0)));
      const S = LV.sim(xs, y0); const per = S.period || S.T[S.T.length - 1];
      orbit = S.X.filter((_, i) => S.T[i] <= per + 1e-9);
    }
    const E = LV.extremes(K);
    setRO($("v-ro"), [["k", fmt(K)], ["prede min / max", `${fmt(E.xmin)} / ${fmt(E.xmax)}`], ["predatori min / max", `${fmt(E.ymin)} / ${fmt(E.ymax)}`],
      ["minimo di V", `(${fmt(dom.x0)}, ${fmt(dom.y0)})`]]);
    draw();
  }
  ks.addEventListener("input", () => { K = +ks.value; compute(); });
  $("v-plane").addEventListener("change", () => draw());
  $("v-rot").addEventListener("change", (e) => (view.auto = e.target.checked));
  function draw() {
    if (!dom) return;
    view.begin();
    const { X, Y, zcap } = dom, N = 34;
    const nx = (x) => x / X * 2 - 1, ny = (y) => y / Y * 2 - 1, nz = (z) => Math.min(z, zcap) / zcap * 2 - 1;
    view.box([[0, X], [0, Y], [0, zcap]], ["prede x", "predatori y", "V(x, y)"], [tok("--sp1"), tok("--sp2"), tok("--ink")]);
    const lo = hexRgb(tok("--accent")), hi = hexRgb(tok("--sp3")), paper = hexRgb(tok("--paper"));
    const items = [];
    const xs = Array.from({ length: N + 1 }, (_, i) => X * (0.012 + 0.988 * i / N)), ys = Array.from({ length: N + 1 }, (_, j) => Y * (0.012 + 0.988 * j / N));
    const Z = xs.map((x) => ys.map((y) => LV.V(x, y)));
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) {
      const z = (Z[i][j] + Z[i + 1][j] + Z[i][j + 1] + Z[i + 1][j + 1]) / 4;
      if (Math.max(Z[i][j], Z[i + 1][j], Z[i][j + 1], Z[i + 1][j + 1]) > zcap) continue;
      const t = Math.min(1, Math.sqrt(Math.min(z, zcap) / zcap));
      const col = mix(mix(lo, paper, 0.25), hi, t);
      items.push({ t: "quad", pts: [[nx(xs[i]), ny(ys[j]), nz(Z[i][j])], [nx(xs[i + 1]), ny(ys[j]), nz(Z[i + 1][j])], [nx(xs[i + 1]), ny(ys[j + 1]), nz(Z[i + 1][j + 1])], [nx(xs[i]), ny(ys[j + 1]), nz(Z[i][j + 1])]], fill: rgba(col, 0.93), stroke: rgba(paper, 0.25) });
    }
    if ($("v-plane").checked && K > 0) {
      const M = 8, zk = nz(K), ink = hexRgb(tok("--muted"));
      for (let i = 0; i < M; i++) for (let j = 0; j < M; j++) {
        const a0 = -1 + 2 * i / M, a1 = -1 + 2 * (i + 1) / M, b0 = -1 + 2 * j / M, b1 = -1 + 2 * (j + 1) / M;
        items.push({ t: "quad", pts: [[a0, b0, zk], [a1, b0, zk], [a1, b1, zk], [a0, b1, zk]], fill: rgba(ink, 0.16) });
      }
    }
    const red = tok("--red");
    for (let i = 1; i < orbit.length; i++) {
      const p = orbit[i - 1], q = orbit[i];
      if (p[0] > X || q[0] > X || p[1] > Y || q[1] > Y) continue;
      items.push({ t: "seg", pts: [[nx(p[0]), ny(p[1]), nz(K) + 0.004], [nx(q[0]), ny(q[1]), nz(K) + 0.004]], color: red, w: 3, bias: 0.05 });
    }
    items.push({ t: "dot", pts: [[nx(dom.x0), ny(dom.y0), -1]], color: tok("--ink"), r: 4.5, ring: tok("--paper"), label: "minimo" });
    view.render(items);
    // mini contour
    mini.set({ x0: 0, x1: X, y0: 0, y1: Y, xc: tok("--sp1"), yc: tok("--sp2") });
    mini.frame(); mini.clip();
    const lv = [0.04, 0.12, 0.25, 0.45, 0.7, 1].map((f) => f * zcap);
    mini.heat(LV.V, lv, null);
    if (orbit.length) mini.path(orbit, red, 2.2);
    mini.dot(dom.x0, dom.y0, 4, tok("--ink"), tok("--paper"));
    mini.unclip(); mini.axes();
  }
  view.draw = draw;
  LV.listeners.push(setKFromLV); setKFromLV();
  window.LVsetK = (frac) => { if (!dom) domain(); K = frac * +ks.max; ks.value = K; compute(); };
  register({ el: cv, draw, tick(dt) { if (view.auto && !reduceMotion) { view.yaw += dt * 0.35; draw(); } } });
  io.observe(cv);
})();

/* ============================ 4. limited growth ============================ */
(function limited() {
  const cv = $("lim-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "prede x", yl: "predatori y" });
  const ts = new TS($("lim-ts"));
  const P = { al: 1, be: 0.01, ga: 0.4, de: 0.01, ep: 0.005, mu: 0.005 };
  const keys = [["al", 2], ["be", 3], ["ga", 2], ["de", 4], ["ep", 4], ["mu", 4]];
  const PRE = {
    co: ["Coesistenza", { al: 1, be: 0.01, ga: 0.4, de: 0.01, ep: 0.005, mu: 0.005 }],
    ext: ["Estinzione dei predatori", { al: 1, be: 0.01, ga: 1.2, de: 0.01, ep: 0.01, mu: 0.005 }],
    lv: ["Senza limiti (ε = μ = 0)", { al: 1, be: 0.01, ga: 0.4, de: 0.01, ep: 0, mu: 0 }],
  };
  const box = $("lim-presets"); let cur = "co";
  Object.entries(PRE).forEach(([id, [n]]) => { const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = n; b.dataset.id = id; b.onclick = () => { Object.assign(P, PRE[id][1]); cur = id; user = []; sync(); update(); }; box.appendChild(b); });
  const sync = () => keys.forEach(([k]) => ($("lim-" + k).value = P[k]));
  keys.forEach(([k]) => $("lim-" + k).addEventListener("input", (e) => { P[k] = +e.target.value; cur = null; update(); }));
  ["lim-field", "lim-null"].forEach((id) => $(id).addEventListener("change", draw));
  $("lim-clear").onclick = () => { user = []; update(); };
  let user = [], trajs = [], eq = [], X = 1, Y = 1, sel = null;
  const SEEDS = [[0.08, 0.8], [0.8, 0.67], [0.88, 0.07], [0.05, 0.06], [0.45, 0.95]];
  plane.onPick((x, y) => { if (x > 0 && y > 0) { user.push([x, y]); if (user.length > 8) user.shift(); update(true); } });
  const g = (v) => [P.al - P.be * v[1] - P.ep * v[0], -P.ga + P.de * v[0] - P.mu * v[1]];
  function J(x, y) { return [P.al - P.be * y - 2 * P.ep * x, -P.be * x, P.de * y, -P.ga + P.de * x - 2 * P.mu * y]; }
  function cls(x, y) { const j = J(x, y), tr = j[0] + j[3], det = j[0] * j[3] - j[1] * j[2]; return classify2(tr, det, false); }
  function update(keepBounds) {
    keys.forEach(([k, dp]) => ($("lim-" + k).nextElementSibling.value = (+P[k]).toFixed(dp)));
    box.querySelectorAll(".chip").forEach((b) => b.setAttribute("aria-pressed", b.dataset.id === cur));
    const den = P.de * P.be + P.ep * P.mu;
    const p4 = den > 0 ? [(P.al * P.mu + P.ga * P.be) / den, (P.al * P.de - P.ep * P.ga) / den] : null;
    eq = [{ n: "P₁", p: [0, 0], c: cls(0, 0) }];
    if (P.ep > 0) eq.push({ n: "P₃", p: [P.al / P.ep, 0], c: cls(P.al / P.ep, 0) });
    if (p4 && p4[1] > 0) eq.push({ n: "P₄", p: p4, c: cls(p4[0], p4[1]) });
    if (!keepBounds) {
      X = P.ep > 0 ? 1.25 * P.al / P.ep : 3 * P.ga / P.de;
      if (p4 && p4[1] > 0) X = Math.max(X, 1.6 * p4[0]);
      Y = 1.5 * Math.max(P.al / P.be * (P.ep > 0 ? 1 : 1.4), p4 && p4[1] > 0 ? p4[1] : 0);
      plane.set({ x0: 0, x1: X, y0: 0, y1: Y });
    }
    const starts = SEEDS.map(([a, b]) => [a * X, b * Y]).concat(user);
    trajs = starts.map((s) => simLog(g, s, 0.04, 6000, 2, (v, t) => t > 60 && Math.abs(g(v)[0]) + Math.abs(g(v)[1]) < 1e-7));
    sel = trajs.length - 1 >= SEEDS.length ? trajs.length - 1 : 1;
    const cond = P.al * P.de - P.ga * P.ep;
    if (P.ep === 0 && P.mu === 0) setStatus($("lim-status"), "warn", "Modello classico", "Senza termini di saturazione le orbite tornano chiuse.");
    else if (cond > 0) { const c4 = eq.find((e) => e.n === "P₄"); setStatus($("lim-status"), "good", "Coesistenza", `αδ = ${fmt(P.al * P.de)} > γε = ${fmt(P.ga * P.ep)}: P₄ è un ${c4 ? c4.c.name.toLowerCase() : "attrattore"} e attira le orbite.`); }
    else setStatus($("lim-status"), "bad", "Estinzione dei predatori", `αδ = ${fmt(P.al * P.de)} < γε = ${fmt(P.ga * P.ep)}: P₃ è un nodo stabile e le orbite finiscono sull'asse x.`);
    const s = trajs[sel], lastX = s.X[s.X.length - 1];
    setRO($("lim-ro"), eq.map((e) => [e.n + " " + e.c.name.toLowerCase(), `(${fmt(e.p[0])}, ${fmt(e.p[1])})`]).concat([["stato finale (traiettoria evidenziata)", `(${fmt(lastX[0])}, ${fmt(lastX[1])})`]]));
    draw();
  }
  function draw() {
    plane.set({ xc: tok("--sp1"), yc: tok("--sp2") });
    plane.frame(); plane.clip();
    if ($("lim-field").checked) plane.field((x, y) => [x * g([x, y])[0], y * g([x, y])[1]], 22);
    if ($("lim-null").checked) {
      if (P.be > 0) plane.path([[0, P.al / P.be], [X * 2, (P.al - P.ep * X * 2) / P.be]], tok("--sp1"), 1.5, 0.9, [7, 5]);
      if (P.mu > 0) plane.path([[0, -P.ga / P.mu], [X * 2, (P.de * X * 2 - P.ga) / P.mu]], tok("--sp2"), 1.5, 0.9, [7, 5]);
      else plane.path([[P.ga / P.de, 0], [P.ga / P.de, Y * 2]], tok("--sp2"), 1.5, 0.9, [7, 5]);
    }
    trajs.forEach((t, i) => plane.path(t.X, i === sel ? tok("--accent") : tok("--ink"), i === sel ? 2.4 : 1.4, i === sel ? 1 : 0.55));
    trajs.forEach((t, i) => plane.dot(t.X[0][0], t.X[0][1], 3, tok("--paper"), i === sel ? tok("--accent") : tok("--muted")));
    eq.forEach((e) => plane.dot(Math.max(e.p[0], X * 0.004), Math.max(e.p[1], Y * 0.006), 5.5, e.c.kind === "good" ? tok("--good") : e.c.kind === "bad" ? tok("--bad") : tok("--warn"), tok("--paper"), e.n));
    plane.unclip(); plane.axes();
    const s = trajs[sel];
    ts.draw(s.T, [{ y: s.X.map((v) => v[0]), color: tok("--sp1"), label: "prede x" }, { y: s.X.map((v) => v[1]), color: tok("--sp2"), label: "predatori y" }]);
  }
  register({ el: cv, draw }); io.observe(cv);
  sync(); update();
})();

/* ============================ 5. n species ============================ */
(function nspecies() {
  const cv = $("n-cv"); if (!cv) return;
  const view = new View3D(cv, { yaw: -0.8, pitch: 0.35 });
  const ts = new TS($("n-ts"));
  const SP = ["--sp1", "--sp3", "--sp2", "--sp4", "--sp5"];
  const VR = [1, 0.72, 1.53, 1.27], VA = [[1, 1.09, 1.52, 0], [0, 1, 0.44, 1.36], [2.33, 0, 1, 0.47], [1.21, 0.51, 0.35, 1]];
  const PRE = {
    coex: { n: "Due prede e un predatore (5.3.1)", names: ["preda 1", "preda 2", "predatore"], b: [1, 0.8, -0.6], A: [[-0.1, -0.06, -0.5], [-0.05, -0.12, -0.4], [0.12, 0.1, 0]], x0: [2, 2, 0.5], T: 120, dt: 0.02, colors: [0, 1, 2] },
    excl: { n: "Esclusione competitiva", names: ["preda 1", "preda 2", "predatore"], b: [1, 0.6, -1], A: [[-0.1, -0.05, -0.5], [-0.12, -0.1, -0.6], [0.2, 0.1, 0]], x0: [1, 0.2, 0.5], T: 60, dt: 0.01, colors: [0, 1, 2] },
    chain: { n: "Catena alimentare", names: ["preda", "predatore", "superpredatore"], b: [1, -0.3, -0.2], A: [[-0.1, -0.5, 0], [0.3, 0, -0.5], [0, 0.2, 0]], x0: [3, 1, 0.5], T: 120, dt: 0.02, colors: [0, 1, 2] },
    rps: { n: "Sasso-carta-forbice", names: ["specie 1", "specie 2", "specie 3"], b: [1, 1, 1], A: [[-1, -0.8, -1.3], [-1.3, -1, -0.8], [-0.8, -1.3, -1]], x0: [0.5, 0.3, 0.2], T: 260, dt: 0.02, colors: [0, 1, 2] },
    chaos: { n: "Caos con 4 specie", names: ["specie 1", "specie 2", "specie 3", "specie 4"], b: VR.slice(), A: VA.map((r, i) => r.map((v) => +(-VR[i] * v).toFixed(4))), x0: [0.3, 0.4, 0.3, 0.4], T: 900, dt: 0.02, axes: [0, 1, 2], colors: [0, 1, 2, 3] },
    eco5: { n: "Ecosistema a 5 specie (Fig. 5.7)", names: ["predatore", "preda 1", "preda 2", "preda 3", "preda 4"], b: [-0.4, 1, 0.9, 0.8, 0.7], A: [[-0.05, 0.1, 0.12, 0.1, 0.12], [-0.4, -0.3, 0.1, 0, 0], [-0.4, 0, -0.3, -0.1, 0], [-0.4, 0, 0, -0.3, 0.08], [-0.4, 0, 0, 0, -0.3]], x0: [1, 1, 1, 1, 1], T: 120, dt: 0.02, axes: [0, 1, 2], colors: [2, 0, 1, 3, 4] },
  };
  const box = $("n-presets"); let M = null, cur = null, R = null, twin = null, head = 1, axes = [0, 1, 2];
  ["coex", "excl", "eco5", "chain", "rps", "chaos"].forEach((id) => { const p = PRE[id]; const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = p.n; b.dataset.id = id; b.onclick = () => load(id); box.appendChild(b); });
  document.querySelectorAll("[data-n-preset]").forEach((b) => b.addEventListener("click", () => { load(b.dataset.nPreset); $("lab-n").scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "center" }); }));
  const col = (i) => tok(SP[(M.colors || [0, 1, 2, 3, 4])[i]]);
  function load(id) {
    const p = PRE[id]; cur = id;
    M = { names: p.names.slice(), b: p.b.slice(), A: p.A.map((r) => r.slice()), x0: p.x0.slice(), T: p.T, dt: p.dt, colors: p.colors };
    axes = (p.axes || [0, 1, 2]).slice(); twin = null; buildMatrix(); buildAxes(); run();
  }
  function buildMatrix() {
    const n = M.b.length, m = $("n-mat");
    m.style.gridTemplateColumns = `1.6em repeat(${n + 1}, minmax(0, 1fr))`; m.classList.toggle("wide", n >= 4);
    let h = `<span></span><span class="h">b</span>` + M.b.map((_, j) => `<span class="h">${j + 1}</span>`).join("");
    for (let i = 0; i < n; i++) {
      h += `<span class="h" style="color:${col(i)}">${i + 1}</span><input data-b="${i}" value="${M.b[i]}" inputmode="decimal" aria-label="b${i + 1}">`;
      for (let j = 0; j < n; j++) h += `<input data-i="${i}" data-j="${j}" value="${M.A[i][j]}" inputmode="decimal" aria-label="a${i + 1}${j + 1}">`;
    }
    m.innerHTML = h; paintInputs();
    m.querySelectorAll("input").forEach((inp) => inp.addEventListener("input", () => {
      const v = parseFloat(inp.value.replace(",", ".")); if (!isFinite(v)) return;
      if (inp.dataset.b != null) M.b[+inp.dataset.b] = v; else M.A[+inp.dataset.i][+inp.dataset.j] = v;
      cur = null; paintInputs(); clearTimeout(buildMatrix.t); buildMatrix.t = setTimeout(run, 160);
    }));
  }
  function paintInputs() { $("n-mat").querySelectorAll("input").forEach((inp) => { const v = parseFloat(inp.value); inp.classList.toggle("pos", v > 0); inp.classList.toggle("neg", v < 0); }); }
  function buildAxes() {
    const n = M.b.length, el = $("n-axes");
    if (n <= 3) { el.innerHTML = ""; return; }
    el.innerHTML = "Assi 3D:" + ["x", "y", "z"].map((a, k) => `<select id="n-ax${k}" aria-label="Specie sull'asse ${a}">${M.names.map((nm, i) => `<option value="${i}" ${axes[k] === i ? "selected" : ""}>${i + 1} · ${nm}</option>`).join("")}</select>`).join("");
    [0, 1, 2].forEach((k) => $("n-ax" + k).addEventListener("change", (e) => { axes[k] = +e.target.value; draw(); }));
  }
  const gfun = () => (x) => M.b.map((bi, i) => bi + M.A[i].reduce((s, a, j) => s + a * x[j], 0));
  function simulate(x0) { const steps = Math.round(M.T / M.dt), every = Math.max(1, Math.round(steps / 2500)); return simLog(gfun(), x0, M.dt, steps, every); }
  function run() {
    box.querySelectorAll(".chip").forEach((b) => b.setAttribute("aria-pressed", b.dataset.id === cur));
    R = simulate(M.x0); if (twin) twin = simulate(twin.x0);
    head = reduceMotion ? R.X.length - 1 : 1;
    analyse(); graph(); draw();
  }
  function analyse() {
    const n = M.b.length, X = R.X, tail = X.slice(Math.floor(X.length * 0.75));
    const maxAll = Math.max(...X.flat());
    const lastv = X[X.length - 1];
    const amp = [...Array(n)].map((_, i) => { const v = tail.map((x) => x[i]); return (Math.max(...v) - Math.min(...v)) / (Math.max(...v) + 1e-12); });
    const extinct = lastv.map((v) => v < 1e-3 * maxAll);
    const xe = solveLin(M.A, M.b.map((v) => -v));
    let eqTxt = "nessuno interno", stab = "", evRows = [];
    if (xe && xe.every((v) => v > 0)) {
      const Jm = M.A.map((r, i) => r.map((a) => a * xe[i])); const ev = eig(Jm); const maxRe = Math.max(...ev.map((e) => e[0]));
      eqTxt = "(" + xe.map((v) => fmt(v)).join(", ") + ")"; stab = maxRe < -1e-9 ? "stabile" : maxRe > 1e-9 ? "instabile" : "marginale";
      evRows = ev.map((e, i) => ["λ" + "₁₂₃₄₅"[i], fmtC(e[0], e[1])]);
    }
    const names = (arr) => arr.map((b, i) => (b ? M.names[i] : null)).filter(Boolean).join(", ");
    if (cur === "chaos") setStatus($("n-status"), "warn", "Dinamica caotica", "Oscillazioni irregolari che non si ripetono mai: traiettorie vicine si separano rapidamente.");
    else if (extinct.some(Boolean)) setStatus($("n-status"), "bad", "Estinzione: " + names(extinct), "Sopravvivono: " + (names(extinct.map((e) => !e)) || "nessuna specie"));
    else if (Math.max(...amp) > 0.05) setStatus($("n-status"), "warn", "Oscillazioni persistenti", "Le popolazioni non si stabilizzano su un equilibrio.");
    else setStatus($("n-status"), "good", "Coesistenza stabile", "Tutte le specie convergono a un equilibrio positivo.");
    const rel = [];
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const a = M.A[i][j], b = M.A[j][i]; if (!a && !b) continue;
      const s = (v) => (v > 0 ? "+" : v < 0 ? "−" : "0");
      let t = a < 0 && b < 0 ? "competizione" : a > 0 && b > 0 ? "mutuo beneficio" : a > 0 && b < 0 ? `${i + 1} mangia ${j + 1}` : a < 0 && b > 0 ? `${j + 1} mangia ${i + 1}` : (a > 0 || b > 0) ? "commensalismo" : "amensalismo";
      rel.push([`${i + 1}–${j + 1} (${s(a)}, ${s(b)})`, t]);
    }
    setRO($("n-ro"), [["equilibrio interno", eqTxt]].concat(stab ? [["stabilità", stab]] : []).concat(evRows).concat(rel.slice(0, 8)));
  }
  function graph() {
    const n = M.b.length, svg = $("n-graph"), W = 300, H = 234, cx = W / 2, cy = H / 2 + 4, r = n <= 3 ? 78 : 88;
    const pos = M.names.map((_, i) => { const a = -Math.PI / 2 + i * 2 * Math.PI / n; return [cx + r * Math.cos(a), cy + r * Math.sin(a)]; });
    const good = tok("--good"), bad = tok("--bad"), mu = tok("--muted");
    let h = `<defs>${["g", "b"].map((k) => `<marker id="ar-${k}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" fill="${k === "g" ? good : bad}"/></marker>`).join("")}</defs>`;
    const NR = 19;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j || !M.A[i][j]) continue;
      // arrow from j (source) to i (target), slightly curved to separate opposite edges
      const [x1, y1] = pos[j], [x2, y2] = pos[i], dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
      const nxv = -uy * 14, nyv = ux * 14, mx = (x1 + x2) / 2 + nxv, my = (y1 + y2) / 2 + nyv;
      const sx = x1 + ux * NR + nxv * 0.25, sy = y1 + uy * NR + nyv * 0.25, ex = x2 - ux * NR + nxv * 0.25, ey = y2 - uy * NR + nyv * 0.25;
      const pos_ = M.A[i][j] > 0, w = 1 + Math.min(3, Math.abs(M.A[i][j]) * 4);
      h += `<path d="M${sx.toFixed(1)} ${sy.toFixed(1)} Q${mx.toFixed(1)} ${my.toFixed(1)} ${ex.toFixed(1)} ${ey.toFixed(1)}" fill="none" stroke="${pos_ ? good : bad}" stroke-width="${w.toFixed(1)}" stroke-opacity=".85" marker-end="url(#ar-${pos_ ? "g" : "b"})"><title>a${i + 1}${j + 1} = ${M.A[i][j]}: la specie ${j + 1} ${pos_ ? "favorisce" : "ostacola"} la ${i + 1}</title></path>`;
    }
    pos.forEach(([x, y], i) => {
      const c = col(i);
      if (M.A[i][i] < 0) h += `<circle cx="${x}" cy="${y}" r="${NR + 4}" fill="none" stroke="${mu}" stroke-dasharray="2 3" stroke-width="1.2"><title>a${i + 1}${i + 1} &lt; 0: competizione interna</title></circle>`;
      h += `<circle cx="${x}" cy="${y}" r="${NR}" fill="${c}" fill-opacity=".16" stroke="${c}" stroke-width="2"/><text x="${x}" y="${y + 1}" text-anchor="middle" dominant-baseline="middle" font-family="IBM Plex Mono, monospace" font-size="13" font-weight="500" fill="${c}">x${i + 1}</text>`;
      const below = y > cy + 5 || (Math.abs(y - cy) <= 5);
      h += `<text x="${x}" y="${y + (y >= cy - 10 ? NR + 14 : -NR - 8)}" text-anchor="middle" font-family="IBM Plex Sans Condensed, Arial, sans-serif" font-size="11" fill="${mu}">${M.names[i]}</text>`;
    });
    svg.innerHTML = h;
  }
  function draw() {
    if (!R) return;
    const n = M.b.length, X = R.X, hi = Math.floor(head);
    const ax = n === 3 ? [0, 1, 2] : axes;
    const all = twin ? X.concat(twin.X) : X;
    const rng = ax.map((k) => [0, Math.max(...all.map((v) => v[k])) * 1.08 || 1]);
    const N = (v) => ax.map((k, i) => v[k] / rng[i][1] * 2 - 1);
    view.begin();
    view.box(rng, ax.map((k) => `x${k + 1} ${M.names[k]}`), ax.map((k) => col(k)));
    const items = [], acc = hexRgb(tok("--accent")), muted = hexRgb(tok("--muted"));
    const path = (Xs, color, upto, wmax) => {
      const step = Math.max(1, Math.floor(Xs.length / 1600));
      for (let i = step; i <= upto; i += step) {
        const t = i / Xs.length; items.push({ t: "seg", pts: [N(Xs[i - step]), N(Xs[i])], color: rgba(mix(muted, color, 0.5 + 0.5 * t), 1), w: wmax * (0.6 + 0.4 * t) });
      }
    };
    path(X, acc, Math.min(hi, X.length - 1), 2.2);
    if (twin) path(twin.X, hexRgb(tok("--red")), Math.min(hi, twin.X.length - 1), 2);
    const p = X[Math.min(hi, X.length - 1)];
    items.push({ t: "dot", pts: [N(p)], color: tok("--ink"), r: 5, ring: tok("--paper") });
    items.push({ t: "dot", pts: [N(X[0])], color: tok("--paper"), r: 3.5, ring: tok("--accent") });
    view.render(items);
    const T = R.T.slice(0, hi + 1);
    ts.draw(R.T, M.names.map((nm, i) => ({ y: R.X.map((v) => v[i]), color: col(i), label: `x${i + 1} ${nm}`, w: 1.6 })).concat(twin ? [{ y: twin.X.map((v) => v[ax[0]]), color: tok("--red"), dash: [4, 3], w: 1.4, label: `gemella x${ax[0] + 1}` }] : []), { cursor: R.T[Math.min(hi, R.T.length - 1)] });
  }
  view.draw = draw;
  $("n-new").onclick = () => { M.x0 = M.x0.map((v) => Math.max(0.02, v * (0.4 + Math.random() * 1.3))); twin = null; run(); };
  $("n-twin").onclick = () => { const x = M.x0.slice(); x[0] += 1e-4; twin = { x0: x }; run(); };
  register({ el: cv, draw, tick(dt) {
    if (!R || head >= R.X.length - 1) return;
    head = Math.min(R.X.length - 1, head + dt * R.X.length / 9); draw();
  } });
  io.observe(cv);
  load("coex");
})();

/* ============================ hero ============================ */
(function hero() {
  const cv = $("hero-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "prede x", yl: "predatori y", m: [12, 14, 30, 44] });
  const p = { a: 0.6, b: 0.012, g: 0.5, d: 0.005 }, x0 = p.g / p.d, y0 = p.a / p.b;
  const starts = [[85, 50], [65, 50], [45, 50], [28, 50], [15, 50]];
  const orbits = starts.map(([x, y]) => {
    let ang = 0, prev = Math.atan2(Math.log(y / y0), Math.log(x / x0)), per = null;
    const r = simLog((v) => [p.a - p.b * v[1], -p.g + p.d * v[0]], [x, y], 0.02, 100000, 1, (v, t) => {
      const th = Math.atan2(Math.log(v[1] / y0), Math.log(v[0] / x0)); let d = th - prev; if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI; ang += d; prev = th;
      if (per == null && Math.abs(ang) >= 2 * Math.PI) per = t; return per != null;
    });
    return r.X;
  });
  let xm = 0, ym = 0; orbits.forEach((o) => o.forEach((v) => { xm = Math.max(xm, v[0]); ym = Math.max(ym, v[1]); }));
  plane.set({ x0: 0, x1: xm * 1.08, y0: 0, y1: ym * 1.1 });
  let ph = 0.15;
  function draw() {
    plane.set({ xc: tok("--sp1"), yc: tok("--sp2") });
    plane.frame(); plane.clip();
    plane.field((x, y) => [p.a * x - p.b * x * y, -p.g * y + p.d * x * y], 18);
    const acc = tok("--accent");
    orbits.forEach((o, k) => plane.path(o, acc, k === 3 ? 2.6 : 1.3, k === 3 ? 1 : 0.45));
    plane.dot(x0, y0, 4.5, tok("--red"), tok("--paper"), "equilibrio");
    plane.unclip(); plane.axes(); plane.snapshot(); dyn();
  }
  function dyn() {
    plane.restore(); plane.clip();
    const o = orbits[3], i = Math.floor(ph * o.length) % o.length, q = o[i];
    const tail = []; for (let k = 40; k >= 0; k--) tail.push(o[(i - k * 3 + o.length * 4) % o.length]);
    plane.path(tail, tok("--red"), 3.2, 0.9);
    // guide lines to axes: current prey and predator values
    plane.path([[q[0], 0], [q[0], q[1]]], tok("--sp1"), 1.4, 0.8, [3, 3]);
    plane.path([[0, q[1]], [q[0], q[1]]], tok("--sp2"), 1.4, 0.8, [3, 3]);
    plane.dot(q[0], q[1], 6.5, tok("--ink"), tok("--paper"));
    plane.unclip();
  }
  register({ el: cv, draw, tick(dt) { if (reduceMotion) return; ph = (ph + dt / 9) % 1; if (plane.off) dyn(); else draw(); } });
  io.observe(cv); draw();
})();

/* ============================ generic RK4 (non-log) ============================ */
function sim2(f, p, dt, steps, stop) {
  const pts = [p.slice()], T = [0]; let [x, y] = p;
  for (let s = 1; s <= steps; s++) {
    const k1 = f(x, y), k2 = f(x + dt / 2 * k1[0], y + dt / 2 * k1[1]), k3 = f(x + dt / 2 * k2[0], y + dt / 2 * k2[1]), k4 = f(x + dt * k3[0], y + dt * k3[1]);
    x += dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]); y += dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]);
    pts.push([x, y]); T.push(s * dt);
    if (stop && stop(x, y, s * dt)) break;
  }
  return { pts, T };
}
function eqToggle(box, key) { if (!box) return; box.querySelectorAll("[data-k]").forEach((d) => (d.hidden = d.dataset.k !== key)); }
function chips(box, list, onPick) {
  box.innerHTML = ""; return list.map(([id, label]) => { const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = label; b.dataset.id = id; b.onclick = () => onPick(id); box.appendChild(b); return b; });
}
const press = (box, id) => box && box.querySelectorAll(".chip").forEach((b) => b.setAttribute("aria-pressed", b.dataset.id === id));

/* ============================ Fig 2.1 pendulum ============================ */
(function pendulum() {
  const cv = $("pend-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "θ", yl: "θ'" });
  const ts = new TS($("pend-ts")), an = $("pend-anim");
  let k = 1, cur = [2.2, 0], orbit = null, head = 0;
  const others = [[0.6, 0], [1.3, 0], [-3.1, 1.2], [3.1, -1.2]];
  const f = (th, om) => [om, -k * Math.sin(th)];
  const E = (th, om) => 0.5 * om * om + k * (1 - Math.cos(th));
  function orbitFrom(p) {
    // integrate until the state returns (oscillation) or theta leaves the window (rotation)
    let last = p[1], turns = 0;
    return sim2(f, p, 0.01, 6000, (x, y, t) => {
      if (Math.abs(x) > 2 * Math.PI + 0.3) return true;
      if ((last <= 0 && y > 0) || (last >= 0 && y < 0)) turns++;
      last = y; return turns >= 2 && t > 0.5 && Math.hypot(x - p[0], y - p[1]) < 0.02;
    });
  }
  function update() {
    $("pend-k").nextElementSibling.value = k.toFixed(2);
    orbit = orbitFrom(cur); head = 0;
    const e = E(...cur), osc = e < 2 * k;
    const per = osc && orbit.T.length > 2 ? orbit.T[orbit.T.length - 1] : null;
    setStatus($("pend-status"), osc ? "good" : "warn", osc ? "Ciclo: oscillazione" : "Traiettoria aperta: il pendolo gira", osc ? "L'orbita è una curva chiusa: la soluzione è periodica." : "L'energia supera 2g/l: il pendolo passa sopra il punto più alto e θ cresce senza limite.");
    const thMax = osc ? Math.acos(1 - e / k) : null;
    setRO($("pend-ro"), [["energia (per ml²)", fmt(e)], ["ampiezza θ_max", osc ? fmt(thMax) + " rad (" + fmt(thMax * 180 / Math.PI) + "°)" : "—"],
      ["periodo", per ? fmt(per) : "—"], ["periodo piccole osc. 2π√(l/g)", fmt(2 * Math.PI / Math.sqrt(k))]]);
    draw();
  }
  function draw() {
    const W = 2 * Math.PI, Om = 2.6 * Math.sqrt(k);
    plane.set({ x0: -W, x1: W, y0: -Om, y1: Om });
    plane.frame(); plane.clip();
    plane.field(f, 24);
    // separatrix E = 2k
    const sep = [], sep2 = []; for (let i = 0; i <= 200; i++) { const th = -W + 2 * W * i / 200, v = Math.sqrt(Math.max(0, 2 * (2 * k - k * (1 - Math.cos(th))))); sep.push([th, v]); sep2.push([th, -v]); }
    plane.path(sep, tok("--muted"), 1.2, 0.7, [5, 4]); plane.path(sep2, tok("--muted"), 1.2, 0.7, [5, 4]);
    others.forEach((p) => plane.path(orbitFrom(p).pts, tok("--accent"), 1.2, 0.4));
    if ($("pend-lin").checked && E(...cur) < 2 * k) {
      const e = E(...cur), a = Math.sqrt(2 * e / k), b = Math.sqrt(2 * e), el = [];
      for (let i = 0; i <= 120; i++) { const t = i / 120 * 2 * Math.PI; el.push([a * Math.cos(t), b * Math.sin(t)]); }
      plane.path(el, tok("--red"), 1.6, 0.9, [6, 4]);
    }
    plane.path(orbit.pts, tok("--accent"), 2.6);
    plane.dot(0, 0, 4, tok("--good"), tok("--paper")); plane.dot(Math.PI, 0, 4, tok("--bad"), tok("--paper")); plane.dot(-Math.PI, 0, 4, tok("--bad"), tok("--paper"));
    plane.unclip(); plane.axes(); plane.snapshot(); dyn();
  }
  function dyn() {
    plane.restore(); plane.clip();
    const i = Math.floor(head) % orbit.pts.length, p = orbit.pts[i];
    plane.dot(p[0], p[1], 6.5, tok("--ink"), tok("--paper"));
    plane.unclip();
    // small-angle comparison
    const th0 = cur[0], om0 = cur[1], w = Math.sqrt(k);
    const lin = orbit.T.map((t) => th0 * Math.cos(w * t) + om0 / w * Math.sin(w * t));
    ts.draw(orbit.T, [{ y: orbit.pts.map((q) => q[0]), color: tok("--accent"), label: "θ(t)" }].concat($("pend-lin").checked ? [{ y: lin, color: tok("--red"), dash: [5, 4], w: 1.4, label: "piccole oscillazioni" }] : []), { cursor: orbit.T[i], signed: true });
    // pendulum drawing
    const { ctx: c, w: W, h: H } = setupCanvas(an);
    c.fillStyle = tok("--paper"); c.fillRect(0, 0, W, H);
    const ox = W / 2, oy = H * 0.48, L = Math.min(W, H) * 0.4, th = p[0];
    c.strokeStyle = tok("--rule"); c.setLineDash([3, 4]); c.beginPath(); c.arc(ox, oy, L, 0, 7); c.moveTo(ox, oy); c.lineTo(ox, oy + L * 1.05); c.stroke(); c.setLineDash([]);
    c.fillStyle = tok("--muted"); c.fillRect(ox - 30, oy - 3, 60, 3);
    const bx = ox + L * Math.sin(th), by = oy + L * Math.cos(th);
    c.strokeStyle = tok("--ink"); c.lineWidth = 2; c.beginPath(); c.moveTo(ox, oy); c.lineTo(bx, by); c.stroke();
    c.beginPath(); c.arc(bx, by, 11, 0, 7); c.fillStyle = tok("--accent"); c.fill();
    c.font = "500 11px 'IBM Plex Mono', monospace"; c.fillStyle = tok("--muted"); c.textAlign = "left"; c.fillText("θ = " + (((th + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI).toFixed(2), 8, H - 10);
  }
  plane.onPick((x, y) => { cur = [x, y]; update(); });
  $("pend-k").addEventListener("input", (e) => { k = +e.target.value; update(); });
  $("pend-lin").addEventListener("change", draw);
  register({ el: cv, draw, tick(dt) { if (reduceMotion || !orbit) return; head = (head + dt * 100 * 0.6) % orbit.pts.length; if (plane.off) dyn(); } });
  io.observe(cv); update();
})();

/* ============================ Fig 2.2 trajectory types ============================ */
(function trajTypes() {
  const cv = $("traj-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "x", yl: "y" });
  const box = $("traj-presets");
  const P = {
    ciclo: { label: "(a) Ciclo", f: (x, y) => [0.6 * x - 0.012 * x * y, -0.5 * y + 0.005 * x * y], view: [0, 260, 0, 130], seeds: [[45, 50], [70, 50]], T: 13, title: "Ciclo", sub: "La traiettoria è una curva chiusa: la soluzione è periodica, φ(t + T) = φ(t).", eq: [100, 50] },
    eq: { label: "(b) Punto di equilibrio", f: (x, y) => [-0.3 * x - 1.2 * y, 1.2 * x - 0.3 * y], view: [-3, 3, -3, 3], seeds: [[2.6, 0.4], [-2.6, -0.4], [0.4, -2.6], [-0.4, 2.6]], T: 14, title: "Punto di equilibrio (attrattore)", sub: "Lo zero del campo vettoriale attira le traiettorie: è asintoticamente stabile.", eq: [0, 0] },
    aperta: { label: "(c) Traiettoria aperta", f: (x, y) => [x, -y], view: [-0.5, 3, -0.5, 3], seeds: [[0.02, 2.9], [0.05, 2.9], [0.12, 2.9]], T: 6, title: "Traiettoria aperta", sub: "L'orbita non si chiude e non tende a un equilibrio: arriva dall'infinito e vi ritorna.", eq: [0, 0] },
  };
  let cur = "ciclo", trajs = [], heads = [];
  chips(box, Object.entries(P).map(([k, v]) => [k, v.label]), (id) => { cur = id; user = []; update(); });
  let user = [];
  function update() {
    const p = P[cur]; press(box, cur); eqToggle($("traj-eqs"), cur);
    setStatus($("traj-status"), cur === "eq" ? "good" : cur === "ciclo" ? "warn" : "", p.title, p.sub);
    plane.set({ x0: p.view[0], x1: p.view[1], y0: p.view[2], y1: p.view[3] });
    trajs = p.seeds.concat(user).map((s) => sim2(p.f, s, 0.01, Math.round(p.T / 0.01), (x, y) => Math.abs(x) > 50 * (p.view[1] - p.view[0]) || Math.abs(y) > 50 * (p.view[3] - p.view[2])).pts);
    heads = trajs.map(() => 0);
    $("traj-note").textContent = cur === "ciclo" ? "Esempio: il modello di Lotka-Volterra (capitolo 4)." : cur === "eq" ? "Esempio: un fuoco stabile (capitolo 3)." : "Esempio: un ramo di sella (capitolo 3).";
    draw();
  }
  function draw() {
    const p = P[cur]; plane.frame(); plane.clip();
    plane.field(p.f, 22);
    trajs.forEach((t) => plane.path(t, tok("--red"), 2));
    plane.dot(p.eq[0], p.eq[1], 5, tok("--ink"), tok("--paper"));
    plane.unclip(); plane.axes(); plane.snapshot(); dyn();
  }
  function dyn() { plane.restore(); plane.clip(); trajs.forEach((t, i) => { const q = t[Math.floor(heads[i]) % t.length]; plane.dot(q[0], q[1], 5, tok("--ink"), tok("--paper")); }); plane.unclip(); }
  plane.onPick((x, y) => { user.push([x, y]); if (user.length > 5) user.shift(); update(); });
  register({ el: cv, draw, tick(dt) { if (reduceMotion || !trajs.length) return; heads = heads.map((h, i) => (h + dt * 100 * 0.9) % trajs[i].length); if (plane.off) dyn(); } });
  io.observe(cv); update();
})();

/* ============================ Theorem 2.7 continuous dependence ============================ */
(function dependence() {
  const cv = $("dep-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "θ", yl: "θ'" });
  const tcv = $("dep-ts");
  let k = 1, x0 = [1.2, 0], d = 1e-3, A = null, B = null;
  const f = (th, om) => [om, -k * Math.sin(th)];
  function update() {
    $("dep-d").nextElementSibling.value = $("dep-d").value; $("dep-k").nextElementSibling.value = k.toFixed(2);
    const dv = [d / Math.SQRT2, d / Math.SQRT2];
    A = sim2(f, x0, 0.005, 6000); B = sim2(f, [x0[0] + dv[0], x0[1] + dv[1]], 0.005, 6000);
    const L = Math.max(1, k); let ok = true, maxRatio = 0;
    A.dist = A.pts.map((p, i) => Math.hypot(p[0] - B.pts[i][0], p[1] - B.pts[i][1]));
    A.bound = A.T.map((t) => Math.exp(L * t) * d);
    A.dist.forEach((v, i) => { if (i && v >= A.bound[i]) ok = false; maxRatio = Math.max(maxRatio, v / A.bound[i]); });
    setStatus($("dep-status"), ok ? "good" : "bad", ok ? "La stima (2.13) è rispettata" : "Stima violata", `La distanza resta sempre sotto e^(L·t)·‖δx₀‖, con L = ${fmt(L)}. Al tempo t = ${fmt(A.T[A.T.length - 1])} la distanza è ${fmt(A.dist[A.dist.length - 1])}.`);
    setRO($("dep-ro"), [["‖δx₀‖", fmt(d)], ["costante di Lipschitz L", fmt(L)], ["distanza finale", fmt(A.dist[A.dist.length - 1])], ["stima finale e^(L·T)·‖δx₀‖", fmt(A.bound[A.bound.length - 1])]]);
    draw();
  }
  function draw() {
    plane.set({ x0: -Math.PI * 1.15, x1: Math.PI * 1.15, y0: -2.4 * Math.sqrt(k), y1: 2.4 * Math.sqrt(k) });
    plane.frame(); plane.clip(); plane.field(f, 22);
    plane.path(A.pts, tok("--accent"), 2.6); plane.path(B.pts, tok("--red"), 1.6, 0.9, [5, 4]);
    plane.dot(x0[0], x0[1], 5, tok("--ink"), tok("--paper"), "x₀");
    plane.unclip(); plane.axes();
    // log plot
    const { ctx: c, w, h } = setupCanvas(tcv); const L0 = 52, R = w - 12, T0 = 10, Bm = h - 26;
    c.fillStyle = tok("--paper"); c.fillRect(0, 0, w, h);
    const lo = Math.floor(Math.log10(d)) - 1, hi = Math.min(Math.ceil(Math.log10(Math.max(...A.bound))) , 3);
    const X = (t) => L0 + t / A.T[A.T.length - 1] * (R - L0), Y = (v) => Bm - (Math.log10(Math.max(v, 1e-30)) - lo) / (hi - lo) * (Bm - T0);
    c.font = "500 11px 'IBM Plex Mono', monospace"; c.textAlign = "right"; c.textBaseline = "middle";
    for (let e = lo; e <= hi; e++) { c.fillStyle = tok("--grid"); c.fillRect(L0, Math.round(Y(Math.pow(10, e))), R - L0, 1); if ((e - lo) % Math.ceil((hi - lo) / 5) === 0) { c.fillStyle = tok("--muted"); c.fillText("10" + String(e).split("").map((ch) => SUP[ch]).join(""), L0 - 6, Y(Math.pow(10, e))); } }
    c.fillStyle = tok("--muted"); c.textAlign = "center"; c.textBaseline = "top"; niceTicks(0, A.T[A.T.length - 1], 6).forEach((t) => c.fillText(tickLabel(t), X(t), Bm + 5));
    c.strokeStyle = tok("--rule"); c.strokeRect(L0 + 0.5, T0 + 0.5, R - L0 - 1, Bm - T0 - 1);
    c.save(); c.beginPath(); c.rect(L0, T0, R - L0, Bm - T0); c.clip();
    const line = (arr, col, wd, dash) => { c.strokeStyle = col; c.lineWidth = wd; c.setLineDash(dash || []); c.beginPath(); arr.forEach((v, i) => { if (i % 4) return; const xx = X(A.T[i]), yy = Y(v); i ? c.lineTo(xx, yy) : c.moveTo(xx, yy); }); c.stroke(); c.setLineDash([]); };
    line(A.bound, tok("--red"), 1.8, [6, 4]); line(A.dist, tok("--accent"), 1.8);
    c.restore();
    c.font = "600 11px 'IBM Plex Sans Condensed', Arial, sans-serif"; c.textAlign = "left"; c.textBaseline = "middle";
    c.fillStyle = tok("--accent"); c.fillRect(L0 + 8, T0 + 10, 12, 3); c.fillText("‖x̃(t) − x(t)‖", L0 + 24, T0 + 11);
    c.fillStyle = tok("--red"); c.fillRect(L0 + 130, T0 + 10, 12, 3); c.fillText("e^(L·t)·‖δx₀‖", L0 + 146, T0 + 11);
  }
  plane.onPick((x, y) => { x0 = [x, y]; update(); });
  $("dep-d").addEventListener("input", (e) => { d = Math.pow(10, +e.target.value); update(); });
  $("dep-k").addEventListener("input", (e) => { k = +e.target.value; update(); });
  register({ el: cv, draw }); io.observe(cv); update();
})();

/* ============================ 3.2 linearization lens ============================ */
(function lens() {
  const cv = $("lens-cv"); if (!cv) return;
  const plane = new Plane(cv, { xl: "θ", yl: "θ'" });
  const box = $("lens-presets");
  let c = 0.3, eqx = 0, zoomE = 0, user = [];
  chips(box, [["0", "Equilibrio (0, 0)"], ["pi", "Equilibrio (π, 0)"]], (id) => { eqx = id === "pi" ? Math.PI : 0; user = []; update(); });
  const f = (th, om) => [om, -Math.sin(th) - c * om];
  function update() {
    press(box, eqx ? "pi" : "0");
    $("lens-z").nextElementSibling.value = "±" + fmt(Math.pow(10, zoomE)); $("lens-c").nextElementSibling.value = c.toFixed(2);
    const J = [0, 1, -Math.cos(eqx), -c], tr = J[0] + J[3], det = J[0] * J[3] - J[1] * J[2], disc = tr * tr - 4 * det;
    const ev = disc >= 0 ? [[(tr + Math.sqrt(disc)) / 2, 0], [(tr - Math.sqrt(disc)) / 2, 0]] : [[tr / 2, Math.sqrt(-disc) / 2], [tr / 2, -Math.sqrt(-disc) / 2]];
    const maxRe = Math.max(ev[0][0], ev[1][0]), cl = classify2(tr, det, false);
    if (maxRe < -1e-9) setStatus($("lens-status"), "good", "Teorema 3.2: asintoticamente stabile", `Tutti gli autovalori hanno parte reale negativa; la linearizzazione è un ${cl.name.toLowerCase()}.`);
    else if (Math.abs(maxRe) <= 1e-9) setStatus($("lens-status"), "warn", "Il Teorema 3.2 non si applica", "Autovalori puramente immaginari: la linearizzazione prevede un centro, ma da sola non decide la stabilità del sistema non lineare (come in Lotka-Volterra).");
    else setStatus($("lens-status"), "bad", cl.name + ": instabile", "Un autovalore ha parte reale positiva: le traiettorie si allontanano dall'equilibrio.");
    setRO($("lens-ro"), [["x₀", eqx ? "(π, 0)" : "(0, 0)"], ["J f(x₀)", `[[${fmt(J[0])}, ${fmt(J[1])}], [${fmt(J[2])}, ${fmt(J[3])}]]`], ["λ₁", fmtC(...ev[0])], ["λ₂", fmtC(...ev[1])]]);
    draw(J);
  }
  function draw(Jin) {
    const J = Jin || [0, 1, -Math.cos(eqx), -c], w = Math.pow(10, zoomE);
    plane.set({ x0: eqx - w, x1: eqx + w, y0: -w, y1: w });
    plane.frame(); plane.clip(); plane.field(f, 20);
    const seeds = []; for (let i = 0; i < 6; i++) { const a = i / 6 * 2 * Math.PI + 0.3; seeds.push([0.85 * w * Math.cos(a), 0.85 * w * Math.sin(a)]); }
    seeds.concat(user.map((p) => [p[0] - eqx, p[1]])).forEach((z) => {
      const out = (x, y) => Math.abs(x - eqx) > 3 * w || Math.abs(y) > 3 * w;
      const nl = sim2(f, [eqx + z[0], z[1]], 0.01, 1400, (x, y) => out(x, y)).pts;
      const ln = sim2((x, y) => [J[0] * x + J[1] * y, J[2] * x + J[3] * y], z, 0.01, 1400, (x, y) => out(x + eqx, y)).pts.map((q) => [q[0] + eqx, q[1]]);
      plane.path(nl, tok("--accent"), 2); plane.path(ln, tok("--red"), 1.6, 0.9, [5, 4]);
      plane.dot(eqx + z[0], z[1], 2.5, tok("--ink"));
    });
    plane.dot(eqx, 0, 5, tok("--ink"), tok("--paper"));
    plane.unclip(); plane.axes();
  }
  plane.onPick((x, y) => { user.push([x, y]); if (user.length > 6) user.shift(); update(); });
  $("lens-z").addEventListener("input", (e) => { zoomE = +e.target.value; update(); });
  $("lens-c").addEventListener("input", (e) => { c = +e.target.value; update(); });
  register({ el: cv, draw: () => draw() }); io.observe(cv); update();
})();

/* ============================ Table 4.1 ============================ */
(function table41() {
  const ids = ["al", "be", "ga", "de", "x", "y"]; if (!$("tab-al")) return;
  const val = (k) => parseFloat($("tab-" + k).value.replace(",", "."));
  function upd() {
    const p = Object.fromEntries(ids.map((k) => [k, val(k)]));
    if (ids.some((k) => !(p[k] > 0))) { $("tab-xmin").textContent = $("tab-ymin").textContent = "—"; $("tab-k").textContent = "Inserisci valori positivi."; return; }
    const x0 = p.ga / p.de, y0 = p.al / p.be;
    const V = (x, y) => p.de * (x - x0) - p.ga * Math.log(x / x0) + p.be * (y - y0) - p.al * Math.log(y / y0);
    const k = V(p.x, p.y);
    const fx = (s) => p.de * Math.exp(s) - p.ga * s - (k + p.de * x0 - p.ga * Math.log(x0));
    const fy = (s) => p.be * Math.exp(s) - p.al * s - (k + p.be * y0 - p.al * Math.log(y0));
    const xmin = k > 0 ? Math.exp(bisect(fx, Math.log(x0) - 800, Math.log(x0))) : x0, ymin = k > 0 ? Math.exp(bisect(fy, Math.log(y0) - 800, Math.log(y0))) : y0;
    $("tab-xmin").textContent = fmt(xmin); $("tab-ymin").textContent = fmt(ymin);
    $("tab-k").innerHTML = `Costante del moto <b>k ≈ ${fmt(k, 4)}</b> · equilibrio (γ/δ, α/β) = (${fmt(x0)}, ${fmt(y0)}). Minimi ottenuti risolvendo (4.26) e (4.27) con il metodo di bisezione.`;
  }
  ids.forEach((k) => $("tab-" + k).addEventListener("input", upd)); upd();
  const ld = $("tab-load");
  if (ld) ld.onclick = () => { if (window.LVload) { window.LVload({ al: val("al"), be: val("be"), ga: val("ga"), de: val("de"), h: 0, x: val("x"), y: val("y") }, true); $("lab-lv").scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "start" }); } };
})();

/* k regimes buttons */
document.querySelectorAll("[data-k]").forEach((b) => {
  if (b.tagName !== "BUTTON") return;
  b.addEventListener("click", () => { if (window.LVsetK) { window.LVsetK(+b.dataset.k); $("lab-v").scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "start" }); } });
});
document.querySelectorAll("[data-lim-preset]").forEach((b) => b.addEventListener("click", () => { const c = document.querySelector(`#lim-presets [data-id="${b.dataset.limPreset}"]`); if (c) { c.click(); $("lab-lim").scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "start" }); } }));

/* ============================ Fig 5.3 quadrants ============================ */
(function quad() {
  const svg = $("quad-svg"); if (!svg) return;
  const A = $("quad-a"), B = $("quad-b");
  const S = 320, M = 30, C = S / 2, R = C - M;
  const types = { pp1: "Preda-predatore: x_i preda, x_j predatore", pp2: "Preda-predatore: x_i predatore, x_j preda", mu: "Mutuo beneficio", co: "Competizione" };
  function draw() {
    const a = +A.value, b = +B.value;
    A.nextElementSibling.value = a.toFixed(2); B.nextElementSibling.value = b.toFixed(2);
    const q = a > 0 && b > 0 ? "mu" : a < 0 && b < 0 ? "co" : a > 0 && b < 0 ? "pp2" : a < 0 && b > 0 ? "pp1" : null;
    const col = { mu: ["--good-bg", "--good"], co: ["--bad-bg", "--bad"], pp1: ["--warn-bg", "--warn"], pp2: ["--warn-bg", "--warn"] };
    const rect = (x, y, id, label, sign, sub) => {
      const on = q === id, [bg, fg] = col[id];
      return `<rect x="${x}" y="${y}" width="${R}" height="${R}" fill="${tok(bg)}" opacity="${on ? 1 : 0.45}" stroke="${on ? tok(fg) : "none"}" stroke-width="2"/>
      <text x="${x + R / 2}" y="${y + R / 2 - 14}" text-anchor="middle" font-family="IBM Plex Sans Condensed, Arial" font-weight="700" font-size="14" fill="${tok(fg)}">${label}</text>
      <text x="${x + R / 2}" y="${y + R / 2 + 8}" text-anchor="middle" font-family="IBM Plex Mono, monospace" font-size="15" fill="${tok(fg)}">${sign}</text>
      <text x="${x + R / 2}" y="${y + R / 2 + 26}" text-anchor="middle" font-family="IBM Plex Sans Condensed, Arial" font-size="10.5" fill="${tok("--muted")}">${sub}</text>`;
    };
    const px = C + a * R, py = C - b * R;
    svg.innerHTML = rect(M, M, "pp1", "Preda-predatore", "(−, +)", "x_i preda, x_j predatore") + rect(C, M, "mu", "Mutuo beneficio", "(+, +)", "") +
      rect(M, C, "co", "Competizione", "(−, −)", "") + rect(C, C, "pp2", "Preda-predatore", "(+, −)", "x_i predatore, x_j preda") +
      `<line x1="${M - 8}" y1="${C}" x2="${S - M + 12}" y2="${C}" stroke="${tok("--ink")}" stroke-width="1.4"/><line x1="${C}" y1="${S - M + 8}" x2="${C}" y2="${M - 12}" stroke="${tok("--ink")}" stroke-width="1.4"/>
      <text x="${S - M - 2}" y="${C - 8}" text-anchor="end" font-family="IBM Plex Mono, monospace" font-size="13" fill="${tok("--ink")}">a_ij</text><text x="${C + 8}" y="${M - 14}" font-family="IBM Plex Mono, monospace" font-size="13" fill="${tok("--ink")}">a_ji</text>
      <circle id="quad-pt" cx="${px}" cy="${py}" r="9" fill="${tok("--accent")}" stroke="${tok("--paper")}" stroke-width="3" style="cursor:grab"/>`;
    setStatus($("quad-status"), q === "mu" ? "good" : q === "co" ? "bad" : q ? "warn" : "", q ? types[q] : "Interazione a senso unico", q ? `a_ij = ${a.toFixed(2)}, a_ji = ${b.toFixed(2)}` : "Uno dei due coefficienti è nullo: solo una specie influenza l'altra.");
  }
  let drag = false;
  const mv = (e) => { const r = svg.getBoundingClientRect(), sx = (e.clientX - r.left) / r.width * S, sy = (e.clientY - r.top) / r.height * S; A.value = clamp((sx - C) / R, -1, 1).toFixed(2); B.value = clamp((C - sy) / R, -1, 1).toFixed(2); draw(); };
  svg.addEventListener("pointerdown", (e) => { drag = true; svg.setPointerCapture(e.pointerId); mv(e); });
  svg.addEventListener("pointermove", (e) => drag && mv(e));
  svg.addEventListener("pointerup", () => (drag = false));
  [A, B].forEach((s) => s.addEventListener("input", draw));
  register({ draw }); draw();
})();

/* ============================ Figs 5.4–5.7 interaction graphs ============================ */
(function nets() {
  const g = $("net-graph"); if (!g) return;
  const box = $("net-presets");
  const mk = (n, list, diag) => { const M = Array.from({ length: n }, () => Array(n).fill(0)); list.forEach(([i, j]) => (M[i - 1][j - 1] = "a")); if (diag) for (let i = 0; i < n; i++) M[i][i] = "a"; return M; };
  const P = {
    f54: { label: "Figura 5.4 · matrice 3 × 3 completa", M: mk(3, [[1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2]], true), cap: "Matrice generica 3 × 3 completa: ogni specie ha degli effetti sulle altre." },
    f55: { label: "Figura 5.5 · triangolare 4 × 4", M: mk(4, [[2, 1], [3, 1], [3, 2], [4, 1], [4, 2], [4, 3]]), cap: "Una matrice triangolare corrisponde a un grafo con un modello gerarchico a cascata, in cui l'influenza fluisce rigorosamente in una sola direzione (dall'intoccabile \"re\" della savana fino alla preda più sfortunata)." },
    f56: { label: "Figura 5.6 · sparsa 4 × 4", M: mk(4, [[1, 2], [2, 4], [3, 2], [3, 4], [4, 3]]), cap: "Come nel caso precedente, il sistema è caratterizzato da una rigida scala gerarchica; la differenza sostanziale risiede nella selettività della predazione. Sebbene la specie x₁ si trovi al vertice della catena alimentare, non è in grado di cibarsi direttamente delle specie x₃ e x₄. Ciò tuttavia non significa che non sia in grado di influenzarle: predando attivamente x₂, la specie x₁ innesca un effetto a cascata che riduce la pressione sui livelli inferiori, permettendo a x₃ e x₄ di proliferare più liberamente." },
    f57: { label: "Figura 5.7 · ecosistema a 5 specie", M: mk(5, [[1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 3], [3, 1], [3, 4], [4, 1], [4, 5], [5, 1]]), cap: "La specie x₁ funge da pilastro centrale, interagendo reciprocamente con le specie periferiche, le quali sono a loro volta connesse da una catena aperta sul perimetro." },
  };
  let cur = "f54", M = null;
  chips(box, Object.entries(P).map(([k, v]) => [k, v.label]), (id) => load(id));
  function load(id) { cur = id; M = P[id].M.map((r) => r.slice()); press(box, id); $("net-cap").textContent = P[id].cap; render(); }
  const sym = (v) => (v === 0 ? "0" : v === "a" ? "a" : v === 1 ? "+" : "−");
  function render() {
    const n = M.length, m = $("net-mat");
    m.style.gridTemplateColumns = `repeat(${n}, minmax(0, 1fr))`;
    m.innerHTML = M.map((r, i) => r.map((v, j) => `<button type="button" class="cell ${v === 1 ? "pos" : v === -1 ? "neg" : v === "a" ? "gen" : ""}" data-i="${i}" data-j="${j}" aria-label="a${i + 1}${j + 1}">${v === 0 ? "0" : `a<sub>${i + 1}${j + 1}</sub>${v === 1 ? "<b>+</b>" : v === -1 ? "<b>−</b>" : ""}`}</button>`).join("")).join("");
    m.querySelectorAll(".cell").forEach((b) => b.onclick = () => { const i = +b.dataset.i, j = +b.dataset.j, v = M[i][j]; M[i][j] = v === 0 ? "a" : v === "a" ? 1 : v === 1 ? -1 : 0; render(); });
    // graph
    const W = 340, H = 280, cx = W / 2, cy = H / 2, r = n === 3 ? 88 : 100, NR = 20;
    const pos = M.map((_, i) => { const a = -Math.PI / 2 + i * 2 * Math.PI / n; return [cx + r * Math.cos(a), cy + r * Math.sin(a)]; });
    const C = { 1: tok("--good"), "-1": tok("--bad"), a: tok("--muted") };
    let h = `<defs>${["1", "-1", "a"].map((k) => `<marker id="na${k === "-1" ? "m" : k}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" fill="${C[k]}"/></marker>`).join("")}</defs>`;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const v = M[i][j]; if (!v || i === j) continue;
      const [x1, y1] = pos[j], [x2, y2] = pos[i], dx = x2 - x1, dy = y2 - y1, L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
      const nx = -uy * 16, ny = ux * 16, mx = (x1 + x2) / 2 + nx, my = (y1 + y2) / 2 + ny;
      const sx = x1 + ux * NR + nx * 0.25, sy = y1 + uy * NR + ny * 0.25, ex = x2 - ux * NR + nx * 0.25, ey = y2 - uy * NR + ny * 0.25, key = String(v);
      h += `<path d="M${sx.toFixed(1)} ${sy.toFixed(1)} Q${mx.toFixed(1)} ${my.toFixed(1)} ${ex.toFixed(1)} ${ey.toFixed(1)}" fill="none" stroke="${C[key]}" stroke-width="1.8" marker-end="url(#na${key === "-1" ? "m" : key})"/>`;
      h += `<text x="${(mx * 0.8 + (x1 + x2) / 2 * 0.2).toFixed(1)}" y="${(my * 0.8 + (y1 + y2) / 2 * 0.2).toFixed(1)}" text-anchor="middle" dominant-baseline="middle" font-family="IBM Plex Mono, monospace" font-size="10" fill="${C[key]}">a${i + 1}${j + 1}</text>`;
    }
    pos.forEach(([x, y], i) => {
      const c = tok(["--sp4", "--sp1", "--sp2", "--sp3", "--sp5"][i % 5]);
      if (M[i][i]) h += `<circle cx="${x}" cy="${y}" r="${NR + 5}" fill="none" stroke="${tok("--muted")}" stroke-dasharray="2 3"/><title>a${i + 1}${i + 1}</title>`;
      h += `<circle cx="${x}" cy="${y}" r="${NR}" fill="${c}" fill-opacity=".15" stroke="${c}" stroke-width="2"/><text x="${x}" y="${y + 1}" text-anchor="middle" dominant-baseline="middle" font-family="IBM Plex Mono, monospace" font-size="13" fill="${c}">x${i + 1}</text>`;
    });
    g.innerHTML = h;
    const rows = [];
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
      const a = M[i][j], b = M[j][i]; if (!a && !b) continue;
      let t;
      if (a === "a" || b === "a") t = a && b ? "reciproca" : "a senso unico";
      else t = a < 0 && b < 0 ? "competizione" : a > 0 && b > 0 ? "mutuo beneficio" : a > 0 && b < 0 ? `x${i + 1} predatore, x${j + 1} preda` : a < 0 && b > 0 ? `x${i + 1} preda, x${j + 1} predatore` : (a > 0 || b > 0) ? "commensalismo" : "amensalismo";
      rows.push([`x${i + 1} – x${j + 1}  (${sym(a)}, ${sym(b)})`, t]);
    }
    setRO($("net-ro"), rows.length ? rows : [["nessuna interazione", ""]]);
  }
  register({ draw: () => M && render() });
  load(cur);
})();

/* ============================ chrome ============================ */
$("theme-btn").addEventListener("click", () => {
  const cur = document.documentElement.dataset.theme || (matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
  const next = cur === "dark" ? "light" : "dark"; document.documentElement.dataset.theme = next;
  try { localStorage.setItem("lv-theme", next); } catch (e) {}
});
(function () {
  const en = $("en-btn"), host = location.hostname;
  if (en && /^https?:$/.test(location.protocol) && host && !/(^localhost$|^127\.|claude|translate\.goog$|\.local$)/.test(host)) {
    en.href = "https://translate.google.com/translate?sl=it&tl=en&u=" + encodeURIComponent(location.href.split("#")[0]); en.hidden = false;
  }
  const links = [...document.querySelectorAll(".secnav a")], secs = links.map((a) => document.querySelector(a.getAttribute("href")));
  const on = () => { let k = -1; secs.forEach((s, i) => { if (s && s.getBoundingClientRect().top < 140) k = i; }); links.forEach((a, i) => a.classList.toggle("on", i === k)); };
  addEventListener("scroll", on, { passive: true }); on();
})();
(function sidenav() {
  const menu = $("menu-btn"), scrim = $("scrim");
  const setNav = (o) => { document.body.classList.toggle("nav-open", o); if (menu) menu.setAttribute("aria-expanded", o); if (scrim) scrim.hidden = !o; };
  if (menu) menu.addEventListener("click", () => setNav(!document.body.classList.contains("nav-open")));
  if (scrim) scrim.addEventListener("click", () => setNav(false));
  document.querySelectorAll(".side-nav ol ol a").forEach((a) => a.addEventListener("click", () => setNav(false)));
  addEventListener("keydown", (e) => { if (e.key === "Escape") setNav(false); });
  const links = [...document.querySelectorAll(".side-nav ol ol a")], targets = links.map((a) => document.getElementById(a.getAttribute("href").slice(1)));
  const on = () => { let k = -1; targets.forEach((t, i) => { if (t && t.getBoundingClientRect().top < 120) k = i; }); links.forEach((a, i) => a.classList.toggle("on", i === k)); };
  addEventListener("scroll", on, { passive: true }); on();
})();
redrawAll();
requestAnimationFrame(loop);
if (document.fonts && document.fonts.ready) document.fonts.ready.then(redrawAll);
})();
