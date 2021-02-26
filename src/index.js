import $ from 'jquery';
import { create, all } from 'mathjs';
import { saveAs } from 'file-saver';
import { initVolumeMeter } from './volume-meter';

const math = create(all);

// colors
const gray = '#cccccc';
const dark = '#000000';

const colors = ['#000000', '#E74C3C', '#2980B9', '#FFA400', '#66E07A', gray];

const fontSmall = '26px Courier';
const fontMenu = '30px Courier';
let fontAnim = '40px Menlo';
const isMac = navigator.platform.toUpperCase().indexOf('MAC') >= 0;
if (!isMac) {
  fontAnim = '40px Courier New';
}

let errorTimer = 0;
const errorText = '';

const scaleFactor = 2; // retina

// scatter
let c;
let ctx;
let winWidth;
let winHeight;

let formulaText;

let objs = [];
let selectedObjs = [];
let frames;
let menu;
let cam;
let pen;
let numFrames = 3;
let frame = 1; // current frame
let nextFrame;
let presenting = false;
let debug = false;
let viewFrame = false;

// speech synthesis
let synth;
let voices;

let tEase = 0;
const tSteps = 30;
let tPercent = 0;
let tInOut = 1.0;

const gridSize = 45;
let mouseTime = 0;
const mouseDuration = 40;

let tool = 'select';
let selecting = false;
let newLine;
let textCopied;

let mouseDown = false;
let tab = false;
let ctrl = false;
let meta = false;
let shift = false;
let mouse = { x: 0, y: 0 };
let mouseLast = { x: 0, y: 0 };
let mouseStart = { x: 0, y: 0 };
let mouseGrid = { x: 0, y: 0 };
let mouseGridLast = { x: 0, y: 0 };
let mouseGraph = { x: 0, y: 0 };

const brackets = {
  '(': 1, '[': 1, ')': -1, ']': -1,
};

let t = 0; // time for parser
let millis = 0;

const pi2 = 2 * Math.PI;
const matNumWidth = 140; // matrix max number width

// fn drawing
const charSize = gridSize / 2;
const charPad = gridSize / 4;

const parser = math.parser();
parser.set('frame', frame);

// custom functions!
function sig(x) {
  return 1 / (1 + math.exp(-x));
}

function sigp(x) {
  return math.exp(-x) / math.pow(1 + math.exp(-x), 2);
}

// http://stackoverflow.com/questions/25582882/javascript-math-random-normal-distribution-gaussian-bell-curve
// Maxwell Collard
function randNBm() {
  const u = 1 - Math.random(); // Subtraction to flip [0, 1) to (0, 1].
  const v = 1 - Math.random();
  return Math.sqrt(-2.0 * Math.log(u)) * Math.cos(2.0 * Math.PI * v);
}

// cache
const matrixCache = {};
function cached(dims) {
  const s = dims.join('_');
  let m = matrixCache[s];
  if (!m) {
    m = math.matrix(math.zeros(dims));
    matrixCache[s] = m;
  }

  return m;
}

// import
function graph(fn, d1, d2, d3) { // graphs y=f(x) from -10 to 10
  let y = 0;
  let p;
  const N = 400;
  let points = cached([N + 1, 3]);
  const asyms = cached([N + 1, 1])._data;
  const pd = points._data;

  const dx = 20 / N;

  let i = 0;
  let x = -10;
  let yLast = fn(x);
  for (; x < 10; x += dx) {
    y = fn(x);

    pd[i][d1] = x;
    pd[i][d2] = Math.max(Math.min(y, 10000), -10000);
    pd[i][d3] = 0;

    asyms[i] = 0;
    if (math.abs(y - yLast) > 20) {
      // vertical asymptote
      asyms[i] = 1;

      pd[i - 1][d2] = math.sign(pd[i - 1][d2]) * 1000;
      pd[i][d2] = math.sign(y) * 1000;
    }

    yLast = y;
    i++;
  }

  points = cam.graph_to_screen_mat(points);

  ctx.beginPath();
  for (let i = 0; i < N; i++) {
    p = points[i];

    if (asyms[i]) {
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(p[0], p[1]);
      continue;
    }

    if (i === 0) {
      ctx.moveTo(p[0], p[1]);
    } else {
      ctx.lineTo(p[0], p[1]);
    }
  }
  ctx.stroke();
}

// graphs x=f(t) y=g(t) z=h(t) from tmin to tmax, units shows markers every 1 increment in t
function para(r, tmin, tmax, units) {
  const N = 300;
  let points = cached([N + 1, 3]);
  const pd = points._data;

  const dt = (tmax - tmin) / N;

  let i = 0;
  let data;

  for (let t = tmin; t <= tmax; t += dt) {
    data = r(t)._data;

    data[0] = Math.max(Math.min(data[0], 1000), -1000);
    data[1] = Math.max(Math.min(data[1], 1000), -1000);
    data[2] = Math.max(Math.min(data[2], 1000), -1000);

    pd[i][0] = data[0];
    pd[i][1] = data[1];
    pd[i][2] = data[2];

    i++;
  }

  points = cam.graph_to_screen_mat(points);

  ctx.beginPath();
  for (let i = 0; i < N; i++) {
    p = points[i];
    if (i === 0) {
      ctx.moveTo(p[0], p[1]);
    } else {
      ctx.lineTo(p[0], p[1]);
    }
  }
  ctx.stroke();

  if (units) {
    let numDots = tmax - tmin;
    numDots = Math.floor(numDots);

    if (numDots > 0) {
      let dots = cached([numDots, 3]);

      let i = 0;

      for (i = 0; i < numDots; i++) {
        data = r(i + 1)._data;

        data[0] = Math.max(Math.min(data[0], 1000), -1000);
        data[1] = Math.max(Math.min(data[1], 1000), -1000);
        data[2] = Math.max(Math.min(data[2], 1000), -1000);

        dots._data[i][0] = data[0];
        dots._data[i][1] = data[1];
        dots._data[i][2] = data[2];
      }

      dots = cam.graph_to_screen_mat(dots);

      ctx.save();
      for (let i = 0; i < numDots; i++) {
        p = dots[i];

        ctx.beginPath();
        ctx.arc(p[0], p[1], 4, 0, pi2);
        ctx.fill();
        ctx.stroke();
      }
      ctx.restore();
    }
  }
}

function implies(p, q) {
  return !p || q;
}

math.import({
  logicTable() {
    O = [true, false];

    for (let k = 0; k < arguments.length; k++) {
      ctx.save();
      s = copy(arguments[k]);

      const props = parser.eval('text_props');
      const { x } = props.p;
      const { y } = props.p;
      ctx.translate(x + 5 * gridSize * k, y + gridSize);
      ctx.fillText(s, 0, 0);

      for (let i = 0; i < 2; i++) {
        p = O[i];

        for (let j = 0; j < 2; j++) {
          q = O[j];

          s.replace('P', p);
          s.replace('Q', q);
          r = math.beval(s);

          if (r) {
            ctx.fillStyle = colors[4];
            ctx.fillText('T', 0, gridSize);
          } else {
            ctx.fillStyle = colors[1];
            ctx.fillText('F', 0, gridSize);
          }

          ctx.beginPath();
          ctx.strokeStyle = colors[5];
          ctx.moveTo(0, gridSize / 2 - 2);
          ctx.lineTo(gridSize * 5, gridSize / 2 - 2);
          ctx.stroke();

          ctx.translate(0, gridSize);
        }
      }

      ctx.restore();
    }
  },
  implies(p, q) { // LOGIC: Returns whether p => q is a true statement. Only false when p=T and q=F
    return implies(p, q);
  },
  beval(statement) { // LOGIC: Boolean evaluation, "true^false||true"
    statement = statement.toLowerCase();
    statement = statement.replace('^', '&&');
    return eval(statement);
  },
  tautology(statement) { // LOGIC: "P&&Q||false" tries all combinations of true and false for p and q, returns true if f is always true
    O = [true, false];

    for (let i = 0; i < 2; i++) {
      p = O[i];
      for (let j = 0; j < 2; j++) {
        q = O[j];

        s = copy(statement);
        s.replace('P', p);
        s.replace('Q', q);

        if (!math.beval(s)) {
          return false;
        }
      }
    }

    return true;
  },
  contradiction(statement) { // LOGIC: "P&&Q||false" tries all combinations of true and false for p and q, returns true if f is always false
    O = [true, false];

    for (let i = 0; i < 2; i++) {
      p = O[i];
      for (let j = 0; j < 2; j++) {
        q = O[j];

        s = copy(statement);
        s.replace('P', p);
        s.replace('Q', q);

        if (math.beval(s)) {
          return false;
        }
      }
    }

    return true;
  },
  egg(f) {
    f = f._data;

    const radius = 100;

    let col = 'white';
    if (f[0]) {
      col = 'white';
    } else if (f[1]) {
      col = colors[3];
    } else if (f[2]) {
      col = colors[4];
    }

    let scol = 'white';
    if (f[3]) {
      scol = 'white';
    } else if (f[4]) {
      scol = colors[3];
    } else if (f[5]) {
      scol = colors[4];
    }

    let spots = 0;
    if (f[6]) {
      spots = 1;
    } else if (f[7]) {
      spots = 3;
    } else if (f[8]) {
      spots = 5;
    }

    const hairy = f[10];

    ctx.save();

    const props = parser.eval('text_props');
    const { x } = props.p;
    const { y } = props.p;
    ctx.translate(x, y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h * 1.2);
    ctx.translate(-x, -y);

    ctx.beginPath();
    ctx.arc(x, y, radius, 0, 2 * math.PI, 0);
    ctx.fillStyle = col;
    ctx.strokeStyle = 'black';
    ctx.fill();
    ctx.stroke();

    const da = 2 * math.PI / math.max(spots, 1);
    for (let i = 0; i < spots; i++) {
      var a = da * i;
      ctx.beginPath();
      ctx.arc(x + math.cos(a) * (20 + spots * 2) + 30,
        y + math.sin(a) * (20 + spots * 2) + 30,
        10, 0, 2 * math.PI, 0);
      ctx.fillStyle = scol;
      ctx.fill();
      ctx.stroke();
    }

    if (hairy) {
      const n = 40;
      const da = 2 * math.PI / n;
      for (let i = 0; i < n; i++) {
        var a = da * i;

        const sx = x + math.cos(a) * radius;
        const sy = y + math.sin(a) * radius;

        ctx.beginPath();

        ctx.moveTo(sx,
          sy);

        ctx.lineTo(sx + math.cos(a) * 15,
          sy + math.sin(a) * 15);

        ctx.stroke();
      }
    }

    ctx.restore();
  },
  rad(deg) { // converts to radians
    return deg * math.pi / 180;
  },
  deg(rad) { // converts to degrees
    return rad * 180.0 / math.pi;
  },
  loop(fn, count) { // function of index 0 to count-1
    if (count <= 0) {
      return;
    }

    for (let i = 0; i < count; i++) {
      fn(i);
    }
  },
  fifo(matrix, value) {
    matrix = matrix._data;
    const N = matrix.length;
    for (let i = 0; i < N - 1; i++) {
      matrix[i] = matrix[i + 1];
    }
    matrix[N - 1] = value;

    return math.matrix(matrix);
  },
  push(matrix, value) {
    matrix = matrix._data;
    matrix.push(value);
    return math.matrix(matrix);
  },
  dims(m) {
    return math.matrix(m.size());
  },
  surface(fn) {
    const d = 21; const d2 = d / 2;
    const dims = [d * d, 3];
    const m = cached(dims);
    let md = m._data;

    let xin = 0; let zin = 0; let yout = 0;
    let i = 0;
    for (let x = 0; x < d; x++) {
      for (let z = 0; z < d; z++) {
        xin = (x - d2) + 0.5;
        zin = (z - d2) + 0.5;
        yout = fn(xin, zin);
        md[i][0] = xin;
        md[i][1] = yout;
        md[i][2] = zin;
        i += 1;
      }
    }

    md = cam.graph_to_screen_mat(m);

    i = 0;
    for (let x = 0; x < d; x++) {
      ctx.beginPath();
      let xc = md[i][0];
      let yc = md[i][1];
      ctx.moveTo(xc, yc);

      for (let z = 0; z < d; z++) {
        xc = md[i][0];
        yc = md[i][1];

        ctx.lineTo(xc, yc);

        i += 1;
      }

      ctx.stroke();

      ctx.beginPath();
      xc = md[x][0];
      yc = md[x][1];
      ctx.moveTo(xc, yc);

      for (let j = 0; j < dims[0]; j += d) {
        xc = md[x + j][0];
        yc = md[x + j][1];

        ctx.lineTo(xc, yc);
      }

      ctx.stroke();
    }
  },
  surfacez(fn) {
    const d = 21; const d2 = d / 2;
    const dims = [d * d, 3];
    const m = cached(dims);
    let md = m._data;

    let a = 0; let b = 0;
    let i = 0;
    for (let x = 0; x < d; x++) {
      for (let z = 0; z < d; z++) {
        a = (x - d2) + 0.5;
        b = (z - d2) + 0.5;
        md[i][0] = a;
        md[i][1] = b;
        md[i][2] = fn(a, b);
        i += 1;
      }
    }

    md = cam.graph_to_screen_mat(m);

    i = 0;
    for (let x = 0; x < d; x++) {
      ctx.beginPath();
      let xc = md[i][0];
      let yc = md[i][1];
      ctx.moveTo(xc, yc);

      for (let z = 0; z < d; z++) {
        xc = md[i][0];
        yc = md[i][1];

        ctx.lineTo(xc, yc);

        i += 1;
      }

      ctx.stroke();

      ctx.beginPath();
      xc = md[x][0];
      yc = md[x][1];
      ctx.moveTo(xc, yc);

      for (let j = 0; j < dims[0]; j += d) {
        xc = md[x + j][0];
        yc = md[x + j][1];

        ctx.lineTo(xc, yc);
      }

      ctx.stroke();
    }
  },
  randn() { // no args: random normal, 1 arg shape: dims of matrix to return
    const N = arguments.length;
    if (N === 1) {
      const shape = arguments[0];
      let m = cached(shape._data);
      m = m.map(() => randNBm());

      return m;
    }
    return randNBm();
  },
  axes(x, y, z) { // replace default camera axis names
    cam.axes_names = [x, y, z];
  },
  block() { // exectutes each argument
  },
  rotation(rx, ry, rz) { // creates a 3x3 rotation matrix
    return math.matrix(rotationMatrix(rx, ry, rz));
  },
  grid(rangex, rangey) { // returns matrix x*y by 2
    if (!rangey) {
      rangey = rangex;
    }

    const xd = rangex._data;
    const yd = rangey._data;
    const xN = xd.length; const yN = yd.length;
    const m = cached([xN * yN, 2]);

    let idx = 0;

    for (let i = 0; i < xN; i++) {
      for (let j = 0; j < yN; j++) {
        const row = m._data[idx];
        row[0] = xd[i];
        row[1] = yd[j];
        idx += 1;
      }
    }

    return m;
  },
  rotateCamera(rx, ry, rz) { // rotates the camera
    const rxyz = [rx, ry, rz];
    if (!isNaN(math.sum(rxyz))) {
      cam.properties[frame].rxyz = rxyz;
    } else {
      cam.properties[frame].rxyz = [0, 0, 0];
    }
  },
  T(m) { // transpose m
    return math.transpose(m);
  },
  scatter(points, pointSize, colorFn) { // points [[x1, y1, z1], ...], psize, color([x,y,z])=[r,g,b] 0 <= r <= 1
    const size = points.size();
    const n = size[0];
    const pointsD = points._data;

    let psize = 8;
    if (arguments.length >= 2) {
      psize = arguments[1];
    }
    const psizeHalf = psize / 2;

    const camData = cam.graph_to_screen_mat(points);

    ctx.save();
    if (arguments.length === 3) {
      // gradation

      const indices = new Array(n);
      for (let i = 0; i < n; ++i) indices[i] = i;

      indices.sort((a, b) => {
        a = camData[a][2];
        b = camData[b][2];
        return a < b ? 1 : (a > b ? -1 : 1);
      });

      let col;
      for (let j = 0; j < n; j++) {
        const i = indices[j];

        const p = pointsD[i];

        // constrain
        col = colorFn(p)._data;
        col = [constrain(col[0]), constrain(col[1]), constrain(col[2])];
        ctx.fillStyle = rgbToHex(math.multiply(col, 255));
        ctx.fillRect(camData[i][0] - psizeHalf, camData[i][1] - psizeHalf, psize, psize);
      }
    } else {
      for (let i = 0; i < n; i++) {
        ctx.fillRect(camData[i][0] - psizeHalf, camData[i][1] - psizeHalf, psize, psize);
      }
    }
    ctx.restore();
  },
  point(a, size, color) { // point [x,y,z] size color[r,g,b]
    let psize = 8;
    if (size) {
      psize = size;
    }

    if (psize <= 0) {
      return;
    }

    if (color) {
      color = color._data;
      color = [constrain(color[0]), constrain(color[1]), constrain(color[2])];
    }

    const camData = cam.graph_to_screen_mat(math.matrix([a]))[0];

    ctx.save();
    ctx.beginPath();
    if (color) {
      ctx.fillStyle = rgbToHex(math.multiply(color, 255));
    }
    ctx.arc(camData[0], camData[1], psize, 0, pi2);
    ctx.fill();

    ctx.restore();
  },
  graph(fn) { // graphs y=f(x)
    graph(fn, 0, 1, 2);
  },
  paral(r, tmin, tmax, units) { // parametric line, graphs r(t)=[f(t), g(t), h(t)] from t=tmin to tmax
    para(r, tmin, tmax, units);
  },
  graphxy(fn) { // graphs y=f(x)
    graph(fn, 0, 1, 2);
  },
  graphyx(fn) { // graphs x=f(y)
    graph(fn, 1, 0, 2);
  },
  graphxz(fn) {
    graph(fn, 0, 2, 1);
  },
  graphyz(fn) {
    graph(fn, 1, 2, 0);
  },
  draw(points, fill) { // draws line from point to point [[x1,y1,z1], ...], draws arrow
    const N = points.size()[0];
    points = cam.graph_to_screen_mat(points);

    ctx.save();
    ctx.beginPath();
    let p;
    for (let i = 0; i < N; i++) {
      p = points[i];
      if (i === 0) {
        ctx.moveTo(p[0], p[1]);
      } else {
        ctx.lineTo(p[0], p[1]);
      }
    }
    ctx.stroke();
    if (fill) {
      col = fill._data;
      col = [constrain(col[0]), constrain(col[1]), constrain(col[2])];
      ctx.fillStyle = rgbToHex(math.multiply(col, 255));
      ctx.globalAlpha = 0.8;
      ctx.fill();
    }
    ctx.restore();
  },
  drawxy(xs, ys) {
    const N = xs.size()[0];
    const m = cached([N, 3]);
    for (let i = 0; i < N; i++) {
      m._data[i][0] = xs._data[i];
      m._data[i][1] = ys._data[i];
      m._data[i][2] = 0;
    }

    math.draw(m);
  },
  oval(_p, hr, vr, _n) {
    let n = 10;
    if (arguments.length >= 4) {
      n = _n;
    }

    const path = [];
    for (let i = 0; i <= n; i++) {
      const t = i / n * 2 * math.PI;
      const p = math.add(_p, [math.cos(t) * hr, math.sin(t) * vr, 0]);
      path.push(p);
    }

    return math.matrix(path);
  },
  vect(a, b) {
    if (!a) {
      return;
    }

    _x = 0;
    _y = 0;
    _z = 0;

    x = 0;
    y = 0;
    z = 0;

    if ('re' in a && a.im) {
      a = math.matrix([a.re, a.im]);
    }

    if (b && b.re && b.im) {
      b = math.matrix([b.re, b.im]);
    }

    if (!b) {
      x = a._data[0];
      y = a._data[1];

      if (a.size()[0] === 3) {
        z = a._data[2];
      }
    } else {
      _x = a._data[0];
      _y = a._data[1];

      if (a.size()[0] === 3) {
        _z = a._data[2];
      }

      x = b._data[0];
      y = b._data[1];

      if (b.size()[0] === 3) {
        z = b._data[2];
      }
    }

    drawVect(_x, _y, _z, x, y, z);
  },
  if(fnCondition, fnA, fnB) { // if fn_condition() == true then fn_a() else fn_b()
    if (fnCondition()) {
      fnA();
    } else {
      fnB();
    }
  },
  list(fn, array) { // [fn(v) for v in array]
    const N = array.size()[0];
    const d = array._data;

    let v = fn(d[0])._data;
    // get return size
    const dims = [N, v.length];

    const m = cached(dims);
    const md = m._data;

    for (let i = 0; i < N; i++) {
      v = fn(d[i]);
      const vd = v._data;

      if (vd) {
        const vN = vd.length;
        for (let j = 0; j < vN; j++) {
          md[i][j] = vd[j];
        }
      } else {
        md[i] = v;
      }
    }

    return m;
  },
  view(x, p) { // matrix, position: [x, y, z]
    let t = [];
    if (x._data) {
      x = x.map((value) => prettyRound(value));

      const d = x._data;
      if (x._size.length === 1) {
        t = [d.join(' ')];
      } else {
        for (let r = 0; r < d.length; r++) {
          t.push(d[r].join(' '));
        }
      }
    }

    if (p) {
      p = p._data;
    } else {
      p = [0, 0];
    }

    p = cam.graph_to_screen(p[0], p[1], 0);
    for (let i = 0; i < t.length; i++) {
      ctx.textAlign = 'left';
      ctx.fillText(t[i], p[0], p[1] + gridSize * i);
    }
  },
  labels(labels, points) { // render labels ["l1", ...] at [[x1, y1, z1], ...]
    points = cam.graph_to_screen_mat(points);
    const N = labels.size()[0];
    let p;
    ctx.save();
    ctx.textAlign = 'center';
    for (let i = 0; i < N; i++) {
      p = points[i];
      ctx.fillText(labels._data[i], p[0], p[1]);
    }
    ctx.restore();
  },
  sig(x) { // sigmoid(x)
    if (x._data) {
      const b = x.map((value) => sig(value));
      return b;
    }

    return sig(x);
  },
  sigp(x) { // sigmoid_prime(x)
    if (x._data) {
      const b = x.map((value) => sigp(value));
      return b;
    }

    return sigp(x);
  },
  field(f, _n, _uv) { // plots a vector field f(x,y,z) using a grid, _n # vectors, _uv force unit length
    let n = 10;
    let uv = false;

    if (arguments.length >= 2) {
      n = _n - 1;

      if (n <= 0) {
        n = 1;
      }
    }

    if (arguments.length >= 3 && _uv === true) {
      uv = true;
    }

    const d = 20 / n;

    for (let x = -10; x <= 10; x += d) {
      for (let y = -10; y <= 10; y += d) {
        for (let z = -10; z <= 10; z += d) {
          let v = f(x, y, z)._data;
          if (uv) {
            const n = math.norm(v);
            v = [v[0] / n, v[1] / n, v[2] / n];
          }

          drawVect(x, y, z, x + v[0], y + v[1], z + v[2]);
        }
      }
    }
  },
  fielda(f, _n, _uv) { // plots an animated vector field f(x,y,z) using a grid, _n # vectors, _uv force unit length
    let n = 10;
    let uv = false;

    const mod = 0.2;
    const flo = (t / 500) % mod;

    if (arguments.length >= 3) {
      n = _n - 1;

      if (n <= 0) {
        n = 1;
      }
    }

    if (arguments.length >= 4 && _uv === true) {
      uv = true;
    }

    const d = 20 / n;

    ctx.save();
    ctx.globalAlpha = math.sin(flo / mod * math.PI);

    for (let x = -10; x <= 10; x += d) {
      for (let y = -10; y <= 10; y += d) {
        for (let z = -10; z <= 10; z += d) {
          let v = f(x, y, z)._data;
          if (uv) {
            const n = math.norm(v);
            v = [v[0] / n, v[1] / n, v[2] / n];
          }

          a = cam.graph_to_screen(x + flo * v[0], y + flo * v[1], z + flo * v[2]);

          ctx.beginPath();
          ctx.arc(a[0], a[1], 5, 0, pi2);
          ctx.fill();
        }
      }
    }
    ctx.restore();
  },
  paras(r, _urs, _ure, _vrs, _vre, _n = 1, f) { // parametric surface r(u,v) with optional field f
    let n = 10;

    if ((_ure - _urs) <= 0 || (_vre - _vrs) <= 0 || n <= 0) {
      return;
    }

    if (arguments.length >= 6) {
      n = _n;
    }

    const du = (_ure - _urs) / n;
    const dv = (_vre - _vrs) / n;

    ctx.save();

    let u = _urs;
    let v = _vrs;

    for (let i = 0; i <= n; i++) {
      u = _urs + du * i;

      ctx.beginPath();
      for (let j = 0; j <= n; j++) {
        v = _vrs + dv * j;

        const p = r(u, v)._data;
        const camp = cam.graph_to_screen(p[0], p[1], p[2]);
        if (v === 0) {
          ctx.moveTo(camp[0], camp[1]);
        } else {
          ctx.lineTo(camp[0], camp[1]);
        }
      }
      ctx.stroke();
    }

    for (let i = 0; i <= n; i++) {
      v = _vrs + dv * i;

      ctx.beginPath();
      for (let j = 0; j <= n; j++) {
        u = _urs + du * j;
        const p = r(u, v)._data;
        const camp = cam.graph_to_screen(p[0], p[1], p[2]);
        if (u === 0) {
          ctx.moveTo(camp[0], camp[1]);
        } else {
          ctx.lineTo(camp[0], camp[1]);
        }
      }
      ctx.stroke();
    }

    if (f) {
      for (let i = 0; i <= n; i++) {
        u = _urs + du * i;

        for (let j = 0; j <= n; j++) {
          v = _vrs + dv * j;

          const p = r(u, v)._data;

          const vect = f(p[0], p[1], p[2])._data;
          drawVect(p[0], p[1], p[2], p[0] + vect[0], p[1] + vect[1], p[2] + vect[2]);
        }
      }
    }

    ctx.restore();
  },
  integral(f, a, b, _n) {
    if (a === b) {
      return 0;
    }

    let negate = false;
    if (a > b) {
      t = b;
      b = a;
      a = t;
      negate = true;
    }

    let n = 10000;
    if (arguments.length >= 4) {
      n = _n;
    }

    const dx = (b - a) / n;
    let sum = 0;
    for (let x = a; x <= b; x += dx) {
      sum += f(x) * dx;
    }

    if (negate) {
      sum *= -1;
    }

    return sum;
  },
  der(f, _h) { // return derivative approximation function _h = dx default .001
    let h = 0.001;
    if (arguments.length >= 2) {
      h = _h;
    }

    return function g(a) {
      return (f(a + h) - f(a)) / h;
    };
  },
  visnet(layers, retHighlighted) { // Draws a neural net layers = [1, 2, 3, 2, 1]
    layers = layers._data;

    const props = parser.eval('text_props');
    const pos = [props.p.x, props.p.y];

    const pad = 200;
    const radius = 20;

    const h = layers.length * pad;
    const w = Math.max(...layers) * pad;

    loc = function (i, j, units) {
      return [pos[0] + 30 + w / 2 - pad * units / 2 + i * pad, pos[1] + h - j * pad - 120];
    };

    ctx.save();

    // connections
    let highConn = [];
    let highNeur = [];

    for (let j = 0; j < layers.length - 1; j++) {
      const units = layers[j];
      const unitsNext = layers[j + 1];

      for (let i = 0; i < units; i++) {
        const p = loc(i, j, units);

        for (let k = 0; k < unitsNext; k++) {
          const p2 = loc(k, j + 1, unitsNext);

          /*
                    let vline = [p2[0] - p[0], p2[1] - p[1]];
                    let mvect = [mouse.x - p[0], mouse.y - p[1]];

                    let dot = mvect[0] * vline[0] + mvect[1] * vline[1];

                    let vlen = math.norm(vline);
                    let total_len = vlen * math.norm(mvect);

                    if (dot > total_len * .998 && dot < vlen*vlen) {
                        ctx.strokeStyle = "red";
                    } else {
                        ctx.strokeStyle = "black";
                    } */

          ctx.strokeStyle = 'black';

          if (highConn.length === 0) {
            const dx1 = p[0] - mouse.x;
            const dy1 = p[1] - mouse.y;

            const dx2 = p2[0] - mouse.x;
            const dy2 = p2[1] - mouse.y;

            const d1 = math.sqrt(dx1 * dx1 + dy1 * dy1);
            const d2 = math.sqrt(dx2 * dx2 + dy2 * dy2);

            const vline = [p2[0] - p[0], p2[1] - p[1]];
            const vlen = math.norm(vline);

            if (d1 + d2 < vlen + 1) {
              ctx.strokeStyle = colors[3];
              highConn = [i, k, j]; // unit i to unit k in layer j
              highNeur = [[i, j], [k, j + 1]];
            }
          }

          ctx.beginPath();
          ctx.moveTo(p[0], p[1]);
          ctx.lineTo(p2[0], p2[1]);
          ctx.stroke();
        }
      }
    }

    ctx.fillStyle = 'white';

    // neurons
    for (let j = 0; j < layers.length; j++) {
      const units = layers[j];

      for (let i = 0; i < units; i++) {
        const p = loc(i, j, units);

        ctx.strokeStyle = 'black';

        // if we have a highlighted connection and we're in the right layer
        if (highConn.length !== 0) {
          if (highConn[2] === j) {
            if (highConn[0] === i) {
              if (j === 0) {
                ctx.strokeStyle = colors[1];
              } else {
                ctx.strokeStyle = colors[2];
              }
            }
          } else if (highConn[2] === j - 1) {
            if (highConn[1] === i) {
              if (j === 0) {
                ctx.strokeStyle = colors[1];
              } else {
                ctx.strokeStyle = colors[2];
              }
            }
          }
        } else {
          const dx = mouse.x - p[0];
          const dy = mouse.y - p[1];

          if (dx * dx + dy * dy < 400) {
            if (j === 0) {
              ctx.strokeStyle = colors[1];
            } else {
              ctx.strokeStyle = colors[2];
            }

            highNeur = [[i, j]];
          }
        }

        ctx.beginPath();
        ctx.arc(p[0], p[1], radius, 0, 2 * Math.PI);
        ctx.fill();
        ctx.stroke();
      }
    }

    ctx.restore();

    if (arguments.length >= 2 && retHighlighted) {
      return [highConn, highNeur];
    }
  },
  int(n) {
    return n | 0;
  },
  elefield(charges, location) { // charges = [q1, x1, y1, z1, q2, x2, y2, z2, etc.], provide location for field there
    charges = charges._data;

    if (arguments.length === 1) {
      n = 5;
      const d = 20 / n;
      let p = [0, 0];
      const pl = 5; // path length

      // let move = ((millis % 1000) /1000 * .5 + .5);
      // console.log(move);

      for (let x = -10; x <= 10; x += d) {
        for (let y = -10; y <= 10; y += d) {
          for (let z = -10; z <= 10; z += d) {
            var xp = x;
            var yp = y;
            var zp = z;

            for (let j = 0; j <= pl; j++) {
              ctx.beginPath();
              p = cam.graph_to_screen(xp, yp, zp);
              ctx.moveTo(p[0], p[1]);
              let dead = false;

              // add up forces from charges
              for (let i = 0; i < charges.length; i += 4) {
                const q = charges[i];
                const cx = charges[i + 1];
                const cy = charges[i + 2];
                const cz = charges[i + 3];

                const v = [xp - cx, yp - cy, zp - cz];
                const len = math.norm(v);
                const l2 = len * len;

                const c = math.coulomb.value * q / len / l2;

                if (len > 2) {
                  xp += c * v[0];
                  yp += c * v[1];
                  zp += c * v[2];
                } else {
                  j = pl;
                  dead = true;
                }
              }

              if (dead === false) {
                p = cam.graph_to_screen(xp, yp, zp);
                ctx.strokeStyle = rgbToHex([math.round((pl - j) / pl * 255), 0, math.round(j / pl * 255)]);
                ctx.lineTo(p[0], p[1]);
                ctx.stroke();
              }
            }
          }
        }
      }
    } else if (arguments.length === 2) {
      // calculate field at the provided location
      loc = location._data;

      var xp = loc[0];
      var yp = loc[1];
      var zp = loc[2];

      let xt = 0;
      let yt = 0;
      let zt = 0;

      // add up forces from charges
      for (let i = 0; i < charges.length; i += 4) {
        const q = charges[i];
        const cx = charges[i + 1];
        const cy = charges[i + 2];
        const cz = charges[i + 3];

        const v = [xp - cx, yp - cy, zp - cz];
        const len = math.norm(v);
        const l2 = len * len;

        const c = math.coulomb.value * q / len / l2; // math.coulomb.value*

        xt += c * v[0];
        yt += c * v[1];
        zt += c * v[2];
      }

      return [xt, yt, zt];
    }
  },
  eleforce(charges, j) { // charges = [q1, x1, y1, z1, q2, x2, y2, z2, etc.] force on jth charge
    charges = charges._data;

    const oc = charges[j * 4];
    const xp = charges[j * 4 + 1];
    const yp = charges[j * 4 + 2];
    const zp = charges[j * 4 + 3];

    let fx = 0;
    let fy = 0;
    let fz = 0;

    // add up forces from charges
    for (let i = 0; i < charges.length; i += 4) {
      if (i === j * 4) {
        continue;
      }

      const q = charges[i];
      const cx = charges[i + 1];
      const cy = charges[i + 2];
      const cz = charges[i + 3];

      const v = [xp - cx, yp - cy, zp - cz];
      const len = math.norm(v);
      const l2 = len * len;

      const c = math.coulomb.value * q * oc / len / l2; // math.coulomb.value*

      fx += c * v[0];
      fy += c * v[1];
      fz += c * v[2];
    }

    return [fx, fy, fz];
  },
  vismult(W, x) { // visualize matrix vector multiplication
    const pad = 24;

    const props = parser.eval('text_props');
    const loc = [props.p.x, props.p.y + pad];

    const result = math.multiply(W, x);

    const xformat = formatMatrix(x._data);
    const rformat = formatMatrix(result._data);
    const Wformat = formatMatrix(W._data);

    const rsize = matrixSize(rformat);
    const Wsize = matrixSize(formatMatrix(W._data));
    const xsize = matrixSize(xformat);

    // draw neural network
    const high = math.visnet(math.matrix([x._size[0], W._size[0]]), true);
    const highConn = high[0];
    const highNeur = high[1];

    // draw matrices

    // draw result matrix
    ctx.save();

    ctx.font = fontAnim;

    ctx.translate(loc[0] + 10, loc[1] + 330);
    drawMatrix(rformat, (i) => {
      ctx.fillStyle = 'black';
      for (let n = 0; n < highNeur.length; n++) {
        const highn = highNeur[n];
        if (highn[1] === 1 && highn[0] === i) {
          ctx.fillStyle = colors[2];
        }
      }
    });

    ctx.fillStyle = 'black';
    ctx.fillText('=', rsize[0] + pad, rsize[1] / 2);

    // draw W matrix
    ctx.translate(rsize[0] + pad * 3, 0);
    drawMatrix(Wformat, (i, j) => {
      ctx.fillStyle = 'black';
      if (highConn.length && highConn[0] === j && highConn[1] === i) {
        ctx.fillStyle = colors[3];
      }
    });

    ctx.fillText('*', Wsize[0] + pad, rsize[1] / 2);

    // draw x matrix
    ctx.translate(Wsize[0] + pad * 3, rsize[1] / 2 - xsize[1] / 2);
    drawMatrix(xformat, (i) => {
      ctx.fillStyle = 'black';

      for (let n = 0; n < highNeur.length; n++) {
        const highn = highNeur[n];
        if (highn[1] === 0 && highn[0] === i) {
          ctx.fillStyle = colors[1];
        }
      }
    });

    ctx.restore();
  },
  visdot(W, x) { // visualize matrix vector multiplication but as dot products
    const pad = 24;

    const props = parser.eval('text_props');
    const loc = [props.p.x, props.p.y + pad];

    const result = math.multiply(W, x);

    const rformat = formatMatrix(result._data);
    const rsize = matrixSize(rformat);

    // draw neural network
    const high = math.visnet(math.matrix([x._size[0], W._size[0]]), true);
    const highNeur = high[1];

    // draw matrices

    // draw result matrix
    ctx.save();

    ctx.font = fontAnim;

    ctx.translate(loc[0] + 10, loc[1] + 330);
    drawMatrix(rformat, (i) => {
      ctx.fillStyle = 'black';
      for (let n = 0; n < highNeur.length; n++) {
        const highn = highNeur[n];
        if (highn[1] === 1 && highn[0] === i) {
          ctx.fillStyle = 'red';
        }
      }
    });

    ctx.fillStyle = 'black';
    ctx.fillText('=', rsize[0] + pad, rsize[1] / 2);

    // draw dot prod matrix
    ctx.translate(rsize[0] + pad * 3, 0);

    let round = prettyRoundOne;
    if (ctrl) {
      round = prettyRound;
    }

    for (let i = 0; i < W._data.length; i++) {
      let text = '';

      for (let j = 0; j < W._data[0].length; j++) {
        text += `${round(W._data[i][j])}*${round(x._data[j])}`;
        if (j < W._data[0].length - 1) {
          text += ' + ';
        }
      }

      ctx.fillText(text, 0, i * gridSize + 20);
    }

    ctx.restore();
  },
  magfield(path, current, AtPoint) { // mag field from path [[x1, y1, z1], [x2, y2, z2], ...]
    n = 5;
    const d = 20 / n;

    const bAt = function (x, y, z, path, current) {
      path = path._data;

      let b = math.zeros(3);
      const c = current * math.magneticConstant.value / 4.0 / math.PI; // u0 I / 4 / pi

      for (let i = 0; i < path.length - 1; i += 1) {
        const p1 = path[i];
        const p2 = path[i + 1];

        let r = math.subtract([x, y, z], p1);
        const rnorm = math.norm(r);
        r = math.multiply(r, 1 / rnorm);

        const ds = math.subtract(p2, p1);
        let db = math.cross(ds, r);
        db = math.multiply(db, 1 / math.pow(rnorm, 2));

        b = math.add(b, db);
      }

      return math.multiply(b, c);
    };

    if (arguments.length >= 3) {
      AtPoint = AtPoint._data;
      const b = bAt(AtPoint[0], AtPoint[1], AtPoint[2], path, current);

      return b;
    }
    for (let x = -10; x <= 10; x += d) {
      for (let y = -10; y <= 10; y += d) {
        for (let z = -10; z <= 10; z += d) {
          let b = bAt(x, y, z, path, current);

          if (math.norm(b) > 0.1) {
            b = b._data;
            drawVect(x, y, z, x + b[0], y + b[1], z + b[2]);
          }
        }
      }
    }
  },
  circle(_p, r, _n) {
    let n = 10;
    if (arguments.length >= 3) {
      n = _n;
    }

    const path = [];
    for (let i = 0; i <= n; i++) {
      const t = i / n * 2 * math.PI;
      const p = math.add(_p, [math.cos(t) * r, math.sin(t) * r, 0]);
      path.push(p);
    }

    return math.matrix(path);
  },
  interp(a, b, divisions) { // interpolate from [x1,y1,z1,...] -> [x2,y2,z2,...]
    ad = a._data;
    bd = b._data;

    divisions -= 1;

    L = cached([divisions + 1, ad.length]);

    for (let i = 0; i <= divisions; i++) {
      const t = i / divisions;
      for (let j = 0; j < ad.length; j++) {
        L._data[i][j] = ad[j] * (1 - t) + t * bd[j];
      }
    }

    return L;
  },
  zer() {
    return [0, 0, 0];
  },
  linspace(a, b, steps) {
    const path = [];

    path.push(a);

    if (steps > 2) {
      const dt = 1 / (steps - 2);
      let t = 0;
      for (let i = 0; i < steps - 2; i++) {
        path.push(math.add(math.multiply(a, (1 - t)), math.multiply(t, b)));
        t += dt;
      }
    }

    path.push(b);

    return math.matrix(path);
  },
  say(text, _voice, _rate, _pitch) { // text to speech
    let voice = 11;

    if (_voice) {
      voice = _voice;
    }

    const utterThis = new SpeechSynthesisUtterance(text);
    utterThis.pitch = 0.8;

    if (arguments.length >= 3) {
      utterThis.rate = _rate;
    }

    if (arguments.length >= 4) {
      utterThis.pitch = _pitch;
    }

    utterThis.voice = voices[voice];
    synth.cancel();
    synth.speak(utterThis);
  },
  enableVolMeter() {
    if (!meterInitialized) {
      meterInitialized = true;
      initVolumeMeter();
    }
  },
  traceToggle() { // enable or disable canvas clearing
    try {
      parser.eval('_trace');
    } catch (e) {
      parser.set('_trace', false);
    }

    parser.set('_trace', !parser.eval('_trace'));
  },
  drawFarmer() {
    ctx.save();

    const props = parser.eval('text_props');
    const { x } = props.p;
    const { y } = props.p;

    ctx.translate(x, y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);
    ctx.translate(-x, -y);

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -1.25, y + -211);
    ctx.rotate(0);
    ctx.scale(4.000000000000001, 4.000000000000001);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -41.25, y + -201);
    ctx.rotate(6.2831853071795845);
    ctx.scale(0.6000000000000001, 0.6000000000000001);
    ctx.arc(0, 0, 20, 1.1102230246251565e-16, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 38.75, y + -201);
    ctx.rotate(-6.2831853071795845);
    ctx.scale(0.6000000000000001, 0.6000000000000001);
    ctx.arc(0, 0, 20, 1.1102230246251565e-16, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -1.25, y + -171);
    ctx.rotate(0);
    ctx.scale(0.6000000000000001, 0.6000000000000001);
    ctx.arc(0, 0, 20, 1.1102230246251565e-16, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -1.25, y + -86);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-20, -45);
    ctx.lineTo(-40, 45);
    ctx.lineTo(40, 45);
    ctx.lineTo(20, -45);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -21.25, y + -21);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, -20);
    ctx.lineTo(0, 20);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 18.75, y + -21);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, -20);
    ctx.lineTo(0, 20);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -36.25, y + -101);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(15, -30);
    ctx.lineTo(-15, 30);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 33.75, y + -101);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-15, -30);
    ctx.lineTo(15, 30);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -57.91666666666674, y + -154.33333333333331);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-23.333333333333258, -56.666666666666686);
    ctx.lineTo(-13.333333333333258, 33.333333333333314);
    ctx.lineTo(36.66666666666674, 23.333333333333314);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 55.41666666666674, y + -154.33333333333331);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(23.333333333333258, -56.666666666666686);
    ctx.lineTo(13.333333333333258, 33.333333333333314);
    ctx.lineTo(-36.66666666666674, 23.333333333333314);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -71.25, y + -291);
    ctx.rotate(-1.308996938995747);
    ctx.scale(4.000000000000001, 3.400000000000001);
    ctx.arc(0, 0, 20, 1.308996938995747, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 68.75, y + -291);
    ctx.rotate(-2.0943951023931953);
    ctx.scale(4.000000000000001, -3.800000000000001);
    ctx.arc(0, 0, 20, 1.308996938995747, 2.8797932657906453, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -86.25, y + -206);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(5, -5);
    ctx.lineTo(-5, 5);
    ctx.restore();
    ctx.stroke();

    ctx.restore();
  },
  drawComputer() {
    ctx.save();

    const props = parser.eval('text_props');
    const { x } = props.p;
    const { y } = props.p;

    ctx.translate(x, y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);
    ctx.translate(-x, -y);

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -3.5, y + -186);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-128, -96);
    ctx.lineTo(-128, 144);
    ctx.lineTo(192, 144);
    ctx.lineTo(192, -96);
    ctx.lineTo(-128, -96);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -151.5, y + -154.5);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(20, -127.5);
    ctx.lineTo(-20, -87.5);
    ctx.lineTo(-20, 102.5);
    ctx.lineTo(20, 112.5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -186.5, y + -124.5);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(15, -77.5);
    ctx.lineTo(-15, -27.5);
    ctx.lineTo(-15, 42.5);
    ctx.lineTo(15, 62.5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -11.5, y + -22);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-40, -20);
    ctx.lineTo(-80, 20);
    ctx.lineTo(80, 20);
    ctx.lineTo(40, -20);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 53.5, y + -187);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(5, 5);
    ctx.lineTo(-5, -5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 98.5, y + -197);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, 5);
    ctx.lineTo(0, -5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 143.5, y + -187);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-5, 5);
    ctx.lineTo(5, -5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 118.5, y + -162);
    ctx.rotate(0);
    ctx.scale(0.20000000000000007, 0.20000000000000007);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 118.5, y + -162);
    ctx.rotate(0);
    ctx.scale(0.6000000000000001, 0.6000000000000001);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 98.5, y + -162);
    ctx.rotate(0);
    ctx.scale(2.1999999999999997, 0.8);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 28.5, y + -122);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.arc(0, 0, 20, 1.1102230246251565e-16, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 0.5, y + -182);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-112, -80);
    ctx.lineTo(-112, 120);
    ctx.lineTo(168, 120);
    ctx.lineTo(168, -80);
    ctx.lineTo(-112, -80);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -41.5, y + -162);
    ctx.rotate(0);
    ctx.scale(2.1999999999999997, 0.8);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -21.5, y + -162);
    ctx.rotate(0);
    ctx.scale(0.6000000000000001, 0.6000000000000001);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -21.5, y + -162);
    ctx.rotate(0);
    ctx.scale(0.20000000000000007, 0.20000000000000007);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 3.5, y + -187);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-5, 5);
    ctx.lineTo(5, -5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -41.5, y + -197);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, 5);
    ctx.lineTo(0, -5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -86.5, y + -187);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(5, 5);
    ctx.lineTo(-5, -5);
    ctx.restore();
    ctx.stroke();

    ctx.restore();
  },
  drawFace() {
    ctx.save();

    const props = parser.eval('text_props');
    const { x } = props.p;
    const { y } = props.p;

    ctx.translate(x, y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);
    ctx.translate(-x, -y);

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -56.25, y + -53.5);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.restore();
    ctx.stroke();

    // pupil
    ctx.save();
    ctx.beginPath();
    let angle = math.atan2(mouse.y - y + 53.5, mouse.x - x + 56.25);
    ctx.translate(x + -56.25, y + -53.5);
    ctx.rotate(angle);
    ctx.translate(8, 0);
    ctx.scale(1, 1);
    ctx.arc(0, 0, 10, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 56.25, y + -53.5);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.arc(0, 0, 20, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    // pupil
    ctx.save();
    ctx.beginPath();
    angle = math.atan2(mouse.y - y + 53.5, mouse.x - x - 56.25);
    ctx.translate(x + 56.25, y + -53.5);
    ctx.rotate(angle);
    ctx.translate(8, 0);
    ctx.scale(1, 1);
    ctx.arc(0, 0, 10, 0, 6.283185307179586, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -8.4375, y + 11.1875);
    ctx.rotate(0);
    if (meter && meter.volume) {
      ctx.scale(1 - meter.volume * 2, 1 + meter.volume * 2);
    } else {
      ctx.scale(1, 1);
    }
    ctx.beginPath();
    ctx.moveTo(-25.3125, -8.4375);
    ctx.lineTo(42.1875, -8.4375);
    ctx.lineTo(8.4375, 25.3125);
    ctx.lineTo(-25.3125, -8.4375);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 0, y + -36.625);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    let np = 28.125;
    if (meter && meter.volume) {
      np -= meter.volume * 20;
    }
    ctx.moveTo(0, -28.125);
    ctx.lineTo(0, np);
    ctx.lineTo(0 - 15, 28.125 - 15);
    ctx.moveTo(0, np);
    ctx.lineTo(0 + 15, 28.125 - 15);
    ctx.restore();
    ctx.stroke();

    ctx.restore();
  },
  drawDog() {
    ctx.save();

    const props = parser.eval('text_props');
    const { x } = props.p;
    const { y } = props.p;

    ctx.translate(x, y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);
    ctx.translate(-x, -y);

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -23.25, y + -117.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-48, -32);
    ctx.lineTo(72, -32);
    ctx.lineTo(72, 48);
    ctx.lineTo(-48, 48);
    ctx.lineTo(-48, -32);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + -51.25, y + -149.75);
    ctx.rotate(0);
    ctx.scale(1, 1.4);
    ctx.arc(0, 0, 20, 0, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.beginPath();
    ctx.translate(x + 28.75, y + -149.75);
    ctx.rotate(0);
    ctx.scale(1, 1.4);
    ctx.arc(0, 0, 20, 0, 3.141592653589795, false);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.translate(x + -42.5, y + -109.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.fillStyle = '#000000';
    ctx.fillText('-', 0, 0);
    ctx.fillText('.', 22.5, 0);
    ctx.fillText('-', 45, 0);
    ctx.restore();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -16.25, y + -94.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(5, -5);
    ctx.lineTo(-5, 5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -6.25, y + -94.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-5, -5);
    ctx.lineTo(5, 5);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -3.75, y + -34.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-37.5, -35);
    ctx.lineTo(-47.5, 35);
    ctx.lineTo(52.5, 35);
    ctx.lineTo(32.5, -35);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -26.25, y + -24.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(5, -25);
    ctx.lineTo(-5, 25);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 63.75, y + -19.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(-15, 20);
    ctx.lineTo(15, -20);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + -1.25, y + -24.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, -25);
    ctx.lineTo(0, 25);
    ctx.restore();
    ctx.stroke();

    ctx.save();
    ctx.globalAlpha = 1;
    ctx.strokeStyle = '#000000';
    ctx.translate(x + 18.75, y + -24.75);
    ctx.rotate(0);
    ctx.scale(1, 1);
    ctx.beginPath();
    ctx.moveTo(0, -25);
    ctx.lineTo(0, 25);
    ctx.restore();
    ctx.stroke();

    ctx.restore();
  },
  dirField(f) { // draws direction field of dy/dx = f(x,y)
    for (let x = -10; x <= 10; x += 2) {
      for (let y = -10; y <= 10; y += 2) {
        dydx = f(x + 0.0001, y + 0.0001); // to avoid asymptotes at x=0 or y=0
        if (dydx.im) {
          continue;
        }
        uv = [1, dydx];
        uv = math.matrix(uv);
        uv = math.multiply(uv, 1 / math.norm(uv));
        drawVect(x, y, 0, x + uv._data[0], y + uv._data[1], 0);
      }
    }
  },
  eulerMeth(f, x0, y0, _n, _h) { // approximate solution to diff eq from initial condition y(x0)=y0, n steps
    n = 10;
    h = 0.1;

    if (_n > 0) {
      n = _n;
    }

    if (_h > 0) {
      h = _h;
    }

    x = x0;
    y = y0;

    ctx.beginPath();

    p = cam.graph_to_screen(x, y, 0);
    ctx.moveTo(p[0], p[1]);

    for (let i = 0; i < n; i++) {
      dydx = f(x, y);

      if (dydx.im) {
        ctx.stroke();
        return math.matrix([x, y]);
      }

      x += h;
      y += dydx * h;

      p = cam.graph_to_screen(x, y, 0);
      ctx.lineTo(p[0], p[1]);
    }

    ctx.stroke();
    return math.matrix([x, y]);
  },
  diffEq(a, b, c, x0, y0, yp0, _n, _dt) { // ay'' + by' + cy = 0 numerically plotted for _n steps and _dt accuracy
    let n = 1000;
    let dt = 0.001;

    if (arguments.length >= 7) {
      n = _n;
    }

    if (arguments.length >= 8) {
      dt = _dt;
    }

    let y = y0;
    let x = x0;
    let yp = yp0;

    let p = cam.graph_to_screen(x, y, 0);

    ctx.beginPath();
    ctx.moveTo(p[0], p[1]);
    for (let i = 0; i < n; i++) {
      ypp = (-b * yp - c * y) / a;
      yp += ypp * dt;
      y += yp * dt;
      x += 1 * dt;
      p = cam.graph_to_screen(x, y, 0);
      ctx.lineTo(p[0], p[1]);
    }
    ctx.stroke();
  },
  diffEqF(a, b, c, f, x0, y0, yp0, _n, _dt) { // ay'' + by' + cy = f(x) numerically plotted for _n steps and _dt accuracy
    let n = 1000;
    let dt = 0.001;

    if (arguments.length >= 8) {
      n = _n;
    }

    if (arguments.length >= 9) {
      dt = _dt;
    }

    let y = y0;
    let x = x0;
    let yp = yp0;

    let p = cam.graph_to_screen(x, y, 0);

    ctx.beginPath();
    ctx.moveTo(p[0], p[1]);
    for (let i = 0; i < n; i++) {
      ypp = (f(x) - b * yp - c * y) / a;
      yp += ypp * dt;
      y += yp * dt;
      x += 1 * dt;
      p = cam.graph_to_screen(x, y, 0);
      ctx.lineTo(p[0], p[1]);
    }
    ctx.stroke();
  },
  diffEqTri(a, b, c, d, x0, y0, yp0, ypp0, _n, _dt) { // ay''' + by'' + cy' + dy = 0 numerically plotted for _n steps and _dt accuracy
    let n = 1000;
    let dt = 0.001;

    if (arguments.length >= 8) {
      n = _n;
    }

    if (arguments.length >= 9) {
      dt = _dt;
    }

    let y = y0;
    let x = x0;
    let yp = yp0;
    let ypp = ypp0;

    let p = cam.graph_to_screen(x, y, 0);

    ctx.beginPath();
    ctx.moveTo(p[0], p[1]);
    for (let i = 0; i < n; i++) {
      yppp = (-b * ypp - c * yp - d * y) / a;
      ypp += yppp * dt;
      yp += ypp * dt;
      y += yp * dt;
      x += 1 * dt;
      p = cam.graph_to_screen(x, y, 0);
      ctx.lineTo(p[0], p[1]);
    }
    ctx.stroke();
  },
  factors(n) { // list positive factors of n
    f = [];
    for (let i = 0; i <= n / 2; i++) {
      if (n / i % 1 === 0) {
        f.push(i);
      }
    }

    f.push(n);

    return math.matrix(f);
  },
  primeFactors(n) { // list prime factors of n
    const factors = math.factors(n);
    const d = factors._data;

    const primes = [];
    // this gonna be real inefficient! fun times...
    for (let i = 0; i < factors._size[0]; i++) {
      const num = d[i];
      const f = math.factors(num);
      if (f._size[0] === 1 || f._size[0] === 2) {
        // prime
        primes.push(num);
      }
    }

    return math.matrix(primes);
  },
  laplace(f, _ti, _tf, _dt) {
    let ti = 0;
    let tf = 1000;
    let dt = 0.01;

    if (arguments.length >= 2) {
      ti = _ti;
    }

    if (arguments.length >= 3) {
      tf = _tf;
    }

    if (arguments.length >= 4) {
      dt = _dt;
    }

    const F = function (s) {
      let sum = 0;
      for (t = ti; t <= tf; t += dt) {
        sum += math.exp(-s * t) * f(t);
      }
      return sum;
    };

    return F;
  },
  step(t) {
    if (t > 0) {
      return 1;
    }
    return 0;
  },
  window(t, a, b) {
    return math.step(t - a) - math.step(t - b);
  },
});

// undo
let states = [];

// http://www.javascriptkit.com/javatutors/requestanimationframe.shtml
window.requestAnimationFrame = window.requestAnimationFrame
    || window.mozRequestAnimationFrame
    || window.webkitRequestAnimationFrame
    || window.msRequestAnimationFrame
    || function (f) { return setTimeout(f, 1000 / fps); }; // simulate calling code 60

// http://stackoverflow.com/questions/105034/create-guid-uuid-in-javascript
function guid() {
  function s4() {
    return Math.floor((1 + Math.random()) * 0x10000)
      .toString(16)
      .substring(1);
  }
  return `${s4() + s4()}-${s4()}-${s4()}-${
    s4()}-${s4()}${s4()}${s4()}`;
}

function prettyRound(num) {
  return (Math.round(num * 100) / 100).toFixed(2);
}

function prettyRoundOne(num) {
  return (Math.round(num * 10) / 10).toFixed(1);
}

function drawR(o, p, d) {
  // o tree object
  // p position
  // d should draw, false to just get the size

  let text = '';
  let argc = 0;
  let args;

  if (o && o.args) {
    args = o.args;
    argc = args.length;
  }

  let size = { w: 0, h: 0 };

  if (args) {
    if (o.name && o.name.length) {
      text = o.name;
    } else if (o.op && o.op.length) {
      text = o.op;
    }

    if (text === '+' || text === '-' || text === '*') {
      if (argc === 1) {
        if (d) ctx.fillText(text, p.x, p.y);
        const s1 = drawR(args[0], { x: p.x + charSize, y: p.y }, d);

        size.w = s1.w + charSize;
        size.h = s1.h;
      } else if (argc === 2) {
        // draw on the left and the right

        const center = false; // false -> bottom align
        let pad2 = charPad * 2;
        if (text === '*') {
          pad2 = 0;
        }

        let s1 = drawR(args[0], { x: 0, y: 0 }, false);
        let s2 = drawR(args[1], { x: 0, y: 0 }, false);

        size.w = s1.w + text.length * charSize + 2 * pad2 + s2.w;
        size.h = Math.max(s1.h, s2.h);

        if (d) {
          let opp = { x: 0, y: 0 };
          if (center) {
            s1 = drawR(args[0], { x: p.x, y: p.y + size.h / 2 - s1.h / 2 }, d);
            opp = { x: p.x + s1.w + pad2, y: p.y + size.h / 2 - charSize };
            s2 = drawR(args[1], { x: p.x + s1.w + pad2 + text.length * charSize + pad2, y: p.y + size.h / 2 - s2.h / 2 }, d);
          } else {
            // bottom align
            s1 = drawR(args[0], { x: p.x, y: p.y + size.h - s1.h }, d);
            opp = { x: p.x + s1.w + pad2, y: p.y + size.h - charSize * 2 };
            s2 = drawR(args[1], { x: p.x + s1.w + pad2 + text.length * charSize + pad2, y: p.y + size.h - s2.h }, d);
          }

          if (text === '*') {
            ctx.beginPath();
            ctx.arc(opp.x + charSize / 2, opp.y + charSize, 3, 0, pi2);
            ctx.fill();
          } else {
            ctx.fillText(text, opp.x, opp.y);
          }
        }
      }
    } else if (text === '^') {
      if (argc === 2) {
        // draw on the left and the right, shifted up!
        const a = args[0];
        let b = args[1];

        if (b.content) {
          b = b.content;
        }

        const s1 = drawR(a, { x: 0, y: 0 }, false);
        const s2 = drawR(b, { x: 0, y: 0 }, false);

        size.w = s1.w + s2.w;
        size.h = s1.h + s2.h - charSize;

        if (d) {
          drawR(a, { x: p.x, y: p.y + size.h - s1.h }, d);
          drawR(b, { x: p.x + s1.w, y: p.y }, d);
        }
      }
    } else if (text === '/') {
      if (argc === 2) {
        // draw on top and bottom
        let a = args[0]; let b = args[1];

        // remove unnecessary parens
        if (a.content) {
          a = a.content;
        }

        if (b.content) {
          b = b.content;
        }

        const s1 = drawR(a, { x: 0, y: 0 }, false);
        const s2 = drawR(b, { x: 0, y: 0 }, false);

        size.w = Math.max(s1.w, s2.w) + charPad * 2;
        size.h = Math.max(s1.h, s2.h) * 2 + charPad * 4;

        if (d) {
          drawR(a, { x: p.x + size.w / 2 - s1.w / 2, y: p.y + size.h / 2 - s1.h - charPad * 2 }, d);
          drawR(b, { x: p.x + size.w / 2 - s2.w / 2, y: p.y + size.h / 2 + charPad * 2 }, d);

          ctx.beginPath();
          ctx.moveTo(p.x, p.y + size.h / 2);
          ctx.lineTo(p.x + size.w, p.y + size.h / 2);
          ctx.stroke();
        }
      }
    } else if (text === '!') {
      const s1 = drawR(args[0], { x: p.x, y: p.y }, d);
      if (d) ctx.fillText(text, p.x + s1.w, p.y);

      size.w = s1.w + charSize;
      size.h = s1.h;
    } else if (o.fn) {
      // function call
      let h = 0;

      // get height of all args
      const N = args.length;
      const hs = [];
      for (let i = 0; i < N; i++) {
        const s1 = drawR(args[i], { x: 0, y: 0 }, false);
        hs.push(s1);

        h = Math.max(h, s1.h);
      }

      size.h = h;

      // draw it
      text = `${o.name}(`;
      const cally = p.y + size.h / 2 - charSize;

      if (d) {
        for (let i = 0; i < text.length; i++) {
          ctx.fillText(text[i], p.x + i * charSize, cally);
        }
      }

      let xo = text.length * charSize;

      for (let i = 0; i < N; i++) {
        const s1 = drawR(args[i], { x: p.x + xo, y: p.y + size.h / 2 - hs[i].h / 2 }, d);
        xo += s1.w;

        if (i === N - 1) {
          if (d) ctx.fillText(')', p.x + xo, cally);
        } else if (d) ctx.fillText(',', p.x + xo, cally);

        xo += charSize;
      }

      size.w = xo;
    }
  } else {
    // no args

    if (o.name && o.name.length) {
      text = o.name;
    } else if (o.value) {
      text = o.value;
    } else {
      text = '?';
    }

    if (o.content) {
      // parens
      let s1 = drawR(o.content, { x: 0, y: 0 }, false);
      // ctx.save();
      // ctx.scale(1, s1.h/(char_size*2));
      if (d) ctx.fillText('(', p.x, p.y + s1.h / 2 - charSize);
      if (d) ctx.fillText(')', p.x + s1.w + charSize, p.y + s1.h / 2 - charSize);
      // ctx.restore();

      s1 = drawR(o.content, { x: p.x + charSize, y: p.y }, d);

      size.w = s1.w + charSize * 2;
      size.h = s1.h;
    } else if (o.node) {
      size = drawR(o.node, { x: p.x, y: p.y }, d);
    } else if (o.object && o.value) {
      // assignment

      const s1 = drawR(o.value, { x: 0, y: 0 }, false);
      const text = `${o.object.name} = `;

      if (d) {
        ctx.save();
        ctx.translate(p.x, p.y + s1.h / 2 - charSize);
        drawSimple(text);
        ctx.restore();

        drawR(o.value, { x: p.x + text.length * charSize, y: p.y }, d);
      }

      size.w = s1.w + text.length * charSize;
      size.h = s1.h;
    } else if (o.blocks) {
      // block

      const items = o.blocks;
      let h = 0;

      // get height of all args
      const N = items.length;
      const hs = [];
      for (let i = 0; i < N; i++) {
        const s1 = drawR(items[i], { x: 0, y: 0 }, false);
        hs.push(s1);

        h = Math.max(h, s1.h);
      }

      size.h = h;

      // draw it
      const cally = p.y + size.h / 2 - charSize;
      let xo = 0;

      for (let i = 0; i < N; i++) {
        const s1 = drawR(items[i], { x: p.x + xo, y: p.y + size.h / 2 - hs[i].h / 2 }, d);
        xo += s1.w;

        if (i !== N - 1) {
          if (d) ctx.fillText(';', p.x + xo, cally);
        }
        xo += charSize;
      }

      xo -= charSize;

      size.w = xo;
    } else if (o.items) {
      // array

      const { items } = o;
      let h = 0;

      // get height of all args
      const N = items.length;
      const hs = [];
      for (let i = 0; i < N; i++) {
        const s1 = drawR(items[i], { x: 0, y: 0 }, false);
        hs.push(s1);

        h = Math.max(h, s1.h);
      }

      size.h = h;

      // draw it
      const cally = p.y + size.h / 2 - charSize;
      let xo = charSize; // first open bracket

      for (let i = 0; i < N; i++) {
        const s1 = drawR(items[i], { x: p.x + xo, y: p.y + size.h / 2 - hs[i].h / 2 }, d);
        xo += s1.w;

        if (i !== N - 1) {
          if (d) ctx.fillText(',', p.x + xo, cally);
        }
        xo += charSize;
      }

      ctx.save();
      ctx.scale(1, size.h / (charSize * 2));
      if (d) ctx.fillText('[', p.x, cally);
      if (d) ctx.fillText(']', p.x + xo - charSize, cally);
      ctx.restore();

      size.w = xo;
    } else if (o.expr) {
      // function definition
      const s1 = drawR(o.expr, { x: 0, y: 0 }, false);

      text = o.name;
      text += `(${o.params.join(',')}) = `;

      if (d) {
        ctx.save();
        ctx.translate(p.x, p.y + s1.h - charSize * 2);
        drawSimple(text);
        ctx.restore();
      }

      const xo = text.length * charSize;

      drawR(o.expr, { x: p.x + xo, y: p.y }, d);

      size.w = xo + s1.w;
      size.h = s1.h;
    } else {
      if (d) {
        const N = text.length;
        for (let i = 0; i < N; i++) {
          ctx.fillText(text[i], p.x + i * charSize, p.y);
        }
      }

      size.w = text.length * charSize;
      size.h = charSize * 2;
    }
  }

  if (debug && d) ctx.strokeRect(p.x, p.y, size.w, size.h);

  return size;
}

function drawVect(_x, _y, _z, x, y, z) {
  a = cam.graph_to_screen(_x, _y, _z);
  b = cam.graph_to_screen(x, y, z);

  a = { x: a[0], y: a[1] };
  b = { x: b[0], y: b[1] };

  ctx.beginPath();
  ctx.moveTo(a.x, a.y);
  ctx.lineTo(b.x, b.y);
  ctx.stroke();

  // draw an arrow head
  const theta = Math.atan2(b.y - a.y, b.x - a.x);

  ctx.beginPath();
  ctx.moveTo(b.x, b.y);
  ctx.lineTo(b.x + Math.cos(theta - Math.PI * 3 / 4) * 15, b.y + Math.sin(theta - Math.PI * 3 / 4) * 15);
  ctx.moveTo(b.x, b.y);
  ctx.lineTo(b.x + Math.cos(theta + Math.PI * 3 / 4) * 15, b.y + Math.sin(theta + Math.PI * 3 / 4) * 15);
  ctx.stroke();
}

function drawBrackets(sx, sy, width, height) {
  ctx.beginPath();
  ctx.moveTo(sx + 7, sy);
  ctx.lineTo(sx, sy);
  ctx.lineTo(sx, sy + height);
  ctx.lineTo(sx + 7, sy + height);
  ctx.stroke();

  ctx.beginPath();
  ctx.moveTo(sx + width - 7, sy);
  ctx.lineTo(sx + width, sy);
  ctx.lineTo(sx + width, sy + height);
  ctx.lineTo(sx + width - 7, sy + height);
  ctx.stroke();
}

function drawSimple(text) {
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '*') {
      ctx.beginPath();
      ctx.arc(i * charSize + charSize / 2, 0, 3, 0, pi2);
      ctx.fill();
    } else {
      ctx.fillText(text[i], i * charSize, 0);
    }
  }
  return text.length * charSize;
}

function drawNetwork(layers, pos) {
  const pad = 120;

  loc = function (i, j, units) {
    const pad2 = 250;
    // return [pos[0] - pad2/2 - j*(pad2+80), pos[1] + pad2/2 - pad2 * units/2 + i*pad2];
    return [pos[0] - pad2 * units / 2 + pad2 / 2 + i * pad2, -pad + pos[1] - j * pad2];
  };

  // connections
  for (let j = 0; j < layers.length - 1; j++) {
    const units = layers[j];
    const unitsNext = layers[j + 1];

    for (let i = 0; i < units; i++) {
      const p = loc(i, j, units);

      for (let k = 0; k < unitsNext; k++) {
        const p2 = loc(k, j + 1, unitsNext);

        const l = new Shape([0, 0, 0, 1], [{ x: p[0], y: p[1] }, { x: p2[0], y: p2[1] }]);
        objs.push(l);
      }
    }
  }

  // neurons
  for (let j = 0; j < layers.length; j++) {
    const units = layers[j];

    for (let i = 0; i < units; i++) {
      const p = loc(i, j, units);
      const c = new Circle([1, 1, 1, 1], { x: p[0], y: p[1] });
      c.properties[frame].fill = [255, 255, 255, 255]; // white fill
      objs.push(c);
    }
  }
}

const cacheFn = {};
function drawFn(fn) {
  let tree;

  if (cacheFn[fn]) {
    tree = cacheFn[fn];
  } else {
    try {
      tree = math.parse(fn);
    } catch (e) {

    }

    if (tree) {
      cacheFn[fn] = tree;
    }
  }

  if (!tree) {
    return { w: 0, h: 0 };
  }

  ctx.save();
  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  const size = drawR(tree, { x: 0, y: 0 }, false);
  drawR(tree, { x: 0, y: -size.h / 2 }, true);
  ctx.restore();

  return size;
}

function matrixSize(matrix) {
  if (matrix && matrix.length === 0) {
    return;
  }

  const pad = 24;

  return [matrix[0].length * (matNumWidth + pad), matrix.length * gridSize];
}

function drawMatrix(matrix, colorIJ) {
  ctx.save();
  ctx.textAlign = 'right';

  const pad = 24;

  let shift = 0;
  if (ctrl) {
    shift = 24;
  }

  const maxWidth = matNumWidth - 10;

  for (let i = 0; i < matrix.length; i++) {
    for (let j = 0; j < matrix[i].length; j++) {
      if (colorIJ) {
        colorIJ(i, j);
      }
      ctx.fillText(matrix[i][j], j * (matNumWidth + pad) + 124 + shift, i * gridSize + 20, maxWidth);
    }
  }

  size = matrixSize(matrix);
  drawBrackets(0, 0, size[0], size[1]);

  ctx.restore();
}

function formatMatrix(matrix) {
  if (matrix.length === 0) {
    return null;
  }

  // format for display
  const formatted = [];
  let round = prettyRoundOne;

  if (ctrl) {
    round = prettyRound;
  }

  if (typeof matrix[0] === 'number') {
    // array
    for (let i = 0; i < matrix.length; i++) {
      formatted.push([round(matrix[i])]);
    }
  } else {
    // matrix
    for (let i = 0; i < matrix.length; i++) {
      const row = [];
      for (let j = 0; j < matrix[i].length; j++) {
        row.push(round(matrix[i][j]));
      }

      formatted.push(row);
    }
  }

  return formatted;
}

function getMousePos(canvas, evt) {
  const rect = canvas.getBoundingClientRect();

  if (evt.touches) {
    for (let i = 0; i < evt.touches.length; i++) {
      if (evt.touches[i].touchType === 'stylus') {
        return {
          x: (evt.touches[i].clientX - rect.left) * scaleFactor,
          y: (evt.touches[i].clientY - rect.top) * scaleFactor,
        };
      }
    }
  }

  return {
    x: (evt.clientX - rect.left) * scaleFactor,
    y: (evt.clientY - rect.top) * scaleFactor,
  };
}

function constrainToGrid(p) {
  const gs = gridSize / 4;
  return { x: Math.floor((p.x + gs / 2) / gs) * gs, y: Math.floor((p.y + gs / 2) / gs) * gs };
}

function distance(a, b) {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function between(a, b) {
  return { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
}

function rotationMatrix(rx, ry, rz) {
  const Rx = [[1, 0, 0],
    [0, Math.cos(rx), -Math.sin(rx)],
    [0, Math.sin(rx), Math.cos(rx)]];

  const Ry = [[Math.cos(ry), 0, Math.sin(ry)],
    [0, 1, 0],
    [-Math.sin(ry), 0, Math.cos(ry)]];

  const Rz = [[Math.cos(rz), -Math.sin(rz), 0],
    [Math.sin(rz), Math.cos(rz), 0],
    [0, 0, 1]];

  return math.multiply(math.multiply(Rx, Ry), Rz);
}

function sigmoid(x, num, offset, width) {
  return num / (1.0 + Math.exp(-(x + offset) * width));
}

function easeInOut(x) {
  return 1.0 / (1.0 + Math.exp(-(x - 0.5) * 10));
}

function copy(d) {
  return JSON.parse(JSON.stringify(d));
}

function changeFrames() {
  for (let i = 0; i < objs.length; i++) {
    obj = objs[i];
    if (obj.properties[frame] && obj.properties[nextFrame] == null) {
      obj.properties[nextFrame] = copy(obj.properties[frame]);
      if (nextFrame < frame) {
        // make that shit transparent?
        obj.properties[nextFrame].c[3] = 0.0;
      }
    }
  }
}

function rgbToHex(c) {
  return `#${((1 << 24) + (Math.round(c[0]) << 16) + (Math.round(c[1]) << 8) + Math.round(c[2])).toString(16).slice(1)}`;
}

function hexToRgb(hex) {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return result ? [
    parseInt(result[1], 16),
    parseInt(result[2], 16),
    parseInt(result[3], 16),
  ] : null;
}

function transformProps(key, props, step = 0.2) {
  if (key === 'l') {
    props.w += step;
  } else if (key === 'j') {
    props.w -= step;
  } else if (key === 'i') {
    props.h += step;
  } else if (key === 'k') {
    props.h -= step;
  } else if (key === 'u') {
    props.r -= Math.PI / 12;
  } else if (key === 'o') {
    props.r += Math.PI / 12;
  }

  return props;
}

function interpolate(a, b) {
  if (!b) {
    return a;
  }

  const interp = {};
  for (key in a) {
    if (key === 'p') {
      // interpolate position
      const ap = a[key];
      const bp = b[key];

      interp[key] = {
        x: (1 - tEase) * ap.x + tEase * bp.x,
        y: (1 - tEase) * ap.y + tEase * bp.y,
      };
    } else if (key === 'w' || key === 'h' || key === 'r' || key === 'a_s' || key === 'a_e') {
      // interpolate width, height, or rotation
      const aw = a[key];
      const bw = b[key];
      interp[key] = (1 - tEase) * aw + tEase * bw;
    } else if (key === 'rxyz') {
      const ar = a[key];
      const br = b[key];
      interp[key] = [0, 0, 0];
      for (let i = 0; i < 3; i++) {
        interp[key][i] = (1 - tEase) * ar[i] + tEase * br[i];
      }
    } else if (key === 'c') {
      // interpolate colors
      const ac = a[key];
      const bc = b[key];
      interp[key] = interpolateColors(ac, bc, constrain(tEase));
    } else if (key === 'path') {
      // interpolate paths
      const ap = a[key];
      const bp = b[key];
      const N = ap.length;
      const ip = new Array(N);
      for (let i = 0; i < N; i++) {
        const newp = {
          x: (1 - tEase) * ap[i].x + tEase * bp[i].x,
          y: (1 - tEase) * ap[i].y + tEase * bp[i].y,
        };
        ip[i] = newp;
      }

      interp[key] = ip;
    } else if (key === 't') {
      if (tEase < 0.5) {
        interp[key] = a[key];
      } else {
        interp[key] = b[key];
      }
    } else {
      interp[key] = a[key];
    }
  }

  return interp;
}

function interpolateColors(ac, bc, interp) {
  let same = true;
  const N = ac.length;
  for (let i = 0; i < N; i++) {
    if (ac[i] !== bc[i]) {
      same = false;
    }
  }

  if (same) {
    return ac;
  }

  const ic = new Array(N);

  for (let i = 0; i < N; i++) {
    ic[i] = (1 - interp) * ac[i] + interp * bc[i];
  }

  return ic;
}

function Button(text, pos, callback) {
  this.text = text;
  this.pos = pos;
  this.callback = callback;
  this.color = '';
  this.align = 'left';
  this.selected = false;

  this.width = text.length * gridSize / 4;
  this.height = gridSize / 4;

  if (this.width === 0) {
    this.width = gridSize;
  }

  this.hovering = function () {
    return (mouse.x > this.pos.x && mouse.x < this.pos.x + this.width && Math.abs(mouse.y - this.pos.y) < this.height);
  };

  this.mouse_up = function () {
    if (this.hovering()) {
      // clicked
      if (this.callback) {
        this.callback(this);
      }
      return true;
    }

    return false;
  };

  this.render = function (ctx) {
    ctx.save();

    ctx.translate(this.pos.x, this.pos.y);

    if (this.hovering() || this.selected) {
      ctx.scale(1.5, 1.5);
    }

    if (this.color.length) {
      ctx.fillStyle = this.color;
      ctx.fillRect(0, -gridSize / 8, gridSize, gridSize / 4);
    }

    ctx.textAlign = this.align;
    ctx.font = fontSmall;
    ctx.fillText(this.text, 0, 0);

    ctx.restore();
  };
}

function Shape(color, path) {
  this.type = 'Shape';
  this.guid = guid();
  this.properties = {};
  this.properties[frame] = {
    c: color, path, v: false, w: 1, h: 1, r: 0,
  };

  this.selected_indices = [];

  this.duplicate = function () {
    if (this.selected_indices.length === 0) {
      return;
    }

    const newc = new Shape(null, null);
    newc.properties[frame] = copy(this.properties[frame]);
    // select all indices for next one
    for (let i = 0; i < newc.properties[frame].path.length; i++) {
      newc.selected_indices.push(i);
    }

    this.selected_indices = [];
    objs.push(newc);
  };

  this.hidden = function () {
    if (!this.properties[frame]) {
      return true;
    }

    return this.properties[frame].c[3] === 0;
  };

  this.copy_properties = function (f, n) {
    this.properties[n] = copy(this.properties[f]);
  };

  this.hide = function () {
    if (this.selected_indices.length !== 0) {
      if (this.properties[frame].c[3] === 1) {
        this.properties[frame].c[3] = 0;
      } else {
        this.properties[frame].c[3] = 1;
      }
      this.selected_indices = [];
    }
  };

  this.select = function () {
    this.selected_indices = [];
    for (let i = 0; i < this.properties[frame].path.length; i++) {
      this.selected_indices.push(i);
    }
  };

  this.is_selected = function () {
    return this.selected_indices.length > 0;
  };

  this.set_color = function (rgba) {
    if (this.selected_indices.length !== 0) {
      rgba[3] = this.properties[frame].c[3];
      this.properties[frame].c = rgba;
    }
  };

  this.clear_props = function (f) {
    delete this.properties[f];
  };

  this.clear_all_props = function () {
    if (this.selected_indices.length === 0) {
      return;
    }

    for (const key in this.properties) {
      if (key !== frame) {
        delete this.properties[key];
      }
    }
  };

  this.del_props_before = function () {
    if (this.selected_indices.length === 0) {
      return;
    }

    if (this.properties && this.properties[frame - 1]) {
      delete this.properties[frame - 1];
    }
  };

  this.add_point = function (p) {
    const props = this.properties[frame];
    const { path } = props;
    path.push(p);
  };

  this.closest_point_idx = function () {
    const props = this.properties[frame];
    const { path } = props;
    for (let i = 0; i < path.length; i++) {
      const p = path[i];

      if (distance(p, mouse) < gridSize / 8) {
        return i;
      }
    }

    return -1;
  };

  this.in_rect = function (x, y, x2, y2) {
    // select individual points
    const props = this.properties[frame];

    if (this.hidden()) {
      return;
    }

    const { path } = props;
    this.selected_indices = [];
    let found = false;

    for (let i = 0; i < path.length; i++) {
      const p = path[i];

      if (p.x > x && p.x < x2 && p.y > y && p.y < y2) {
        this.selected_indices.push(i);
        found = true;
      }
    }

    return found;
  };

  this.onkeydown = function (evt) {
    const { key } = evt;

    if (this.selected_indices.length !== 0) {
      this.properties[frame] = transformProps(key, this.properties[frame]);
    }

    return false;
  };

  this.mouse_down = function () {
    if (this.hidden()) {
      return false;
    }

    // try to selected one
    const idx = this.closest_point_idx();
    if (idx !== -1) {
      this.selected_indices = [idx];
      return true;
    }

    return false;
  };

  this.mouse_drag = function () {
    if (this.selected_indices.length > 0) {
      const props = this.properties[frame];
      const { path } = props;

      if (tool === 'select') {
        // move all
        const offset = {
          x: mouseGrid.x - mouseGridLast.x,
          y: mouseGrid.y - mouseGridLast.y,
        };
        for (let i = 0; i < this.selected_indices.length; i++) {
          const idx = this.selected_indices[i];
          const p = path[idx];
          path[idx] = { x: p.x + offset.x, y: p.y + offset.y };
        }
      }
    }
  };

  this.mouse_up = function () {
    if (!shift) {
      this.selected_indices = [];
    }
  };

  this.bezier = function (points, off, t) {
    let x = points[0].x - off.x;
    let y = points[0].y - off.y;
    let c = 0;
    const N = points.length;
    for (let i = 0; i < N; i++) {
      c = math.factorial(N) / (math.factorial(N - i) * math.factorial(i));

      c *= math.pow(1 - t, N - i) * math.pow(t, i);

      x += c * (points[i].x - off.x);
      y += c * (points[i].y - off.y);
    }

    return [x, y];
  };

  this.draw_path = function (props) {
    const { path } = props;
    const c = { x: 0, y: 0 };

    for (let i = 0; i < path.length; i++) {
      c.x += path[i].x;
      c.y += path[i].y;
    }

    c.x /= path.length;
    c.y /= path.length;

    ctx.translate(c.x, c.y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);

    const idx = this.closest_point_idx();

    const hidden = this.hidden();

    for (let i = 0; i < path.length; i++) {
      const p = path[i];

      if (i === 0) {
        ctx.moveTo(p.x - c.x, p.y - c.y);
      } else {
        ctx.lineTo(p.x - c.x, p.y - c.y);
      }

      // show selected indices
      if (!presenting && !hidden && (this.selected_indices.indexOf(i) !== -1 || i === idx)) {
        ctx.strokeStyle = dark;
        ctx.strokeRect(p.x - c.x - gridSize / 2, p.y - c.y - gridSize / 2, gridSize, gridSize);
      }
    }

    if (this.selected_indices.length > 0) {
      // render side lengths while dragging
      for (let i = 0; i < path.length - 1; i++) {
        const p1 = path[i];
        const p2 = path[i + 1];
        const b = between(p1, p2);
        let d = distance(p1, p2) / gridSize;
        d = Math.round(d * 10) / 10;
        ctx.fillText(d, b.x - c.x, b.y - c.y);
      }
    }

    if (this.properties[frame].v && path.length >= 2) {
      // vector
      const b = path[path.length - 2];
      const a = path[path.length - 1];

      const theta = Math.atan2(a.y - b.y, a.x - b.x);
      ctx.moveTo(a.x - c.x, a.y - c.y);
      ctx.lineTo(a.x - c.x + Math.cos(theta - Math.PI * 3 / 4) * gridSize / 2, a.y - c.y + Math.sin(theta - Math.PI * 3 / 4) * gridSize / 2);
      ctx.moveTo(a.x - c.x, a.y - c.y);
      ctx.lineTo(a.x - c.x + Math.cos(theta + Math.PI * 3 / 4) * gridSize / 2, a.y - c.y + Math.sin(theta + Math.PI * 3 / 4) * gridSize / 2);
    }
  };

  this.generate_javascript = function () {
    const cp = cam.properties[frame].p;

    const props = this.properties[frame];
    const { path } = props;
    const c = { x: 0, y: 0 };

    for (let i = 0; i < path.length; i++) {
      c.x += path[i].x;
      c.y += path[i].y;
    }

    c.x /= path.length;
    c.y /= path.length;

    js = '';
    js += 'ctx.save();\n';
    js += `ctx.globalAlpha = ${props.c[3]};\n`;
    js += `ctx.strokeStyle = "${rgbToHex(props.c)}";\n`;
    js += `ctx.translate(x + ${c.x - cp.x}, y + ${c.y - cp.y});\n`;
    js += `ctx.rotate(${props.r});\n`;
    js += `ctx.scale(${props.w}, ${props.h});\n`;
    js += 'ctx.beginPath();\n';

    for (let i = 0; i < path.length; i++) {
      const p = path[i];

      if (i === 0) {
        js += `ctx.moveTo(${p.x - c.x}, ${p.y - c.y});\n`;
      } else {
        js += `ctx.lineTo(${p.x - c.x}, ${p.y - c.y});\n`;
      }
    }

    js += 'ctx.restore();\n';
    js += 'ctx.stroke();\n';

    return js;
  };

  this.render = function (ctx) {
    const a = this.properties[frame];
    const b = this.properties[nextFrame];

    if (!a) {
      return;
    }

    let props;
    if (transition.transitioning) {
      props = interpolate(a, b);
    } else {
      props = a;
    }

    ctx.save();
    ctx.beginPath();
    ctx.globalAlpha = props.c[3];
    ctx.strokeStyle = rgbToHex(props.c);
    this.draw_path(props);
    ctx.stroke();
    ctx.restore();
  };
}

function Circle(color, pos) {
  this.type = 'Circle';
  this.guid = guid();
  this.properties = {};
  this.properties[frame] = {
    p: pos, c: color, fill: [0, 0, 0, 0], a_s: 0, a_e: Math.PI * 2.0, w: 1, h: 1, r: 0,
  };
  this.selected = false;

  this.select = function () {
    this.selected = true;
  };

  this.is_selected = function () {
    return this.selected;
  };

  this.hidden = function () {
    if (!this.properties[frame]) {
      return true;
    }

    return this.properties[frame].c[3] === 0;
  };

  this.copy_properties = function (f, n) {
    this.properties[n] = copy(this.properties[f]);
  };

  this.duplicate = function () {
    if (!this.selected) {
      return;
    }

    const newc = new Circle(null, null);
    newc.properties[frame] = copy(this.properties[frame]);
    newc.selected = true;
    this.selected = false;
    objs.push(newc);
  };

  this.hide = function () {
    if (this.selected) {
      if (this.properties[frame].c[3] === 1) {
        this.properties[frame].c[3] = 0;
      } else {
        this.properties[frame].c[3] = 1;
      }
      this.selected = false;
    }
  };

  this.set_color = function (rgba) {
    if (this.selected) {
      rgba[3] = this.properties[frame].c[3];
      this.properties[frame].c = rgba;
    }
  };

  this.clear_props = function (f) {
    delete this.properties[f];
  };

  this.clear_all_props = function () {
    if (!this.selected) {
      return;
    }

    for (const key in this.properties) {
      if (key !== frame) {
        delete this.properties[key];
      }
    }
  };

  this.del_props_before = function () {
    if (!this.selected) {
      return;
    }

    if (this.properties && this.properties[frame - 1]) {
      delete this.properties[frame - 1];
    }
  };

  this.near_mouse = function () {
    const props = this.properties[frame];
    if (!props) {
      return false;
    }

    return distance(props.p, mouse) < gridSize / 2;
  };

  this.in_rect = function (x, y, x2, y2) {
    if (this.hidden()) {
      return false;
    }

    const props = this.properties[frame];
    const { p } = props;

    if (p.x > x && p.x < x2 && p.y > y && p.y < y2) {
      this.selected = true;
      return true;
    }

    return false;
  };

  this.onkeydown = function (evt) {
    if (!this.selected) {
      return false;
    }

    const { key } = evt;

    if (ctrl) {
      const p = this.properties[frame];
      const step = Math.PI / 12;
      if (key === 'u') {
        p.a_s += step;
      } else if (key === 'o') {
        p.a_s -= step;
      } else if (key === 'j') {
        p.a_e -= step;
      } else if (key === 'l') {
        p.a_e += step;
      }
    } else {
      this.properties[frame] = transformProps(key, this.properties[frame]);
    }

    return false;
  };

  this.mouse_down = function (evt) {
    if (this.hidden()) {
      return false;
    }

    // try to selected one
    if (this.near_mouse()) {
      this.selected = true;
      return true;
    }

    return false;
  };

  this.mouse_drag = function (evt) {
    if (this.selected && tool === 'select') {
      // move
      const props = this.properties[frame];
      const offset = {
        x: mouseGrid.x - mouseGridLast.x,
        y: mouseGrid.y - mouseGridLast.y,
      };
      const { p } = props;
      this.properties[frame].p = { x: p.x + offset.x, y: p.y + offset.y };
    }
  };

  this.mouse_up = function (evt) {
    if (!shift) {
      this.selected = false;
    }
  };

  this.draw_ellipse = function (props, ctx) {
    const { p } = props;
    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);
    ctx.arc(0, 0, 20, props.a_s, props.a_e, false);
    ctx.restore();
  };

  this.generate_javascript = function () {
    const props = this.properties[frame];
    const { p } = props;
    const cp = cam.properties[frame].p;

    let js = '';

    js += 'ctx.save();\n';
    js += 'ctx.beginPath();\n';
    js += `ctx.translate(x + ${p.x - cp.x}, y + ${p.y - cp.y});\n`;
    js += `ctx.rotate(${props.r});\n`;
    js += `ctx.scale(${props.w}, ${props.h});\n`;
    js += `ctx.arc(0, 0, 20, ${props.a_s}, ${props.a_e}, false);\n`;
    js += `ctx.globalAlpha = ${props.c[3]};\n`;
    js += `ctx.strokeStyle = "${rgbToHex(props.c)}";\n`;
    js += 'ctx.restore();\n';
    js += 'ctx.stroke();\n';

    return js;
  };

  this.render = function (ctx) {
    const a = this.properties[frame];
    const b = this.properties[nextFrame];

    if (!a) {
      return;
    }

    let props;
    if (transition.transitioning) {
      props = interpolate(a, b);
    } else {
      props = a;
    }

    ctx.beginPath();
    this.draw_ellipse(props, ctx);

    ctx.save();

    ctx.fillStyle = rgbToHex(props.fill);
    ctx.globalAlpha = math.min(props.fill[3], props.c[3]);
    ctx.fill();

    ctx.globalAlpha = props.c[3];
    ctx.strokeStyle = rgbToHex(props.c);

    ctx.stroke();

    ctx.restore();

    if (!presenting && props.c[3] !== 0 && (this.selected || this.near_mouse())) {
      ctx.beginPath();
      ctx.strokeStyle = dark;
      ctx.strokeRect(props.p.x - gridSize / 4, props.p.y - gridSize / 4, gridSize / 2, gridSize / 2);
      ctx.stroke();
    }
  };
}

function Text(text, pos) {
  this.type = 'Text';
  this.guid = guid();
  this.properties = {};
  this.properties[frame] = {
    t: text, p: pos, c: [0, 0, 0, 1], w: 1, h: 1, r: 0,
  };

  // ephemeral
  this.new = true; // loaded or just created
  this.selected = false;
  this.dragged = false;
  this.cursor = 0;
  this.cursor_selection = 0;
  this.command = '';
  this.args = [];
  this.cargs = []; // compiled arguments
  this.text_val = '';
  this.matrix_vals = [];
  this.near_mouse = false;
  this.size = { w: 0, h: 0 }; // pixel width and height
  this.image = null;

  this.select = function () {
    this.selected = true;
    formulaText.value = this.properties[frame].t;
  };

  this.is_selected = function () {
    return this.selected;
  };

  this.selection_indices = function () {
    const s = Math.min(this.cursor, this.cursor_selection);
    const e = Math.max(this.cursor, this.cursor_selection);
    return { s, e };
  };

  this.text_selected = function () {
    if (!this.is_text_selected()) {
      return;
    }

    const props = this.properties[frame];
    if (!props) {
      return;
    }

    const s = this.selection_indices();
    return props.t.slice(s.s, s.e);
  };

  this.is_text_selected = function () {
    return this.cursor !== this.cursor_selection;
  };

  this.replace_selected_text = function (replace) {
    const props = this.properties[frame];
    if (!props) {
      return;
    }

    const text = props.t;
    const s = this.selection_indices();
    const newText = text.slice(0, s.s) + replace + text.slice(s.e, text.length);

    this.cursor = s.s + replace.length;
    this.cursor_selection = this.cursor;

    return newText;
  };

  this.paste_text = function (textCopied) {
    if (this.is_text_selected()) {
      // wipe out some text in between
      this.change_text(this.replace_selected_text(textCopied));
    } else {
      const text = this.properties[frame].t;
      this.properties[frame].t = text.slice(0, this.cursor) + textCopied + text.slice(this.cursor, text.length);
      this.cursor += textCopied.length;
      this.cursor_selection = this.cursor;
    }
  };

  this.constrain_cursors = function () {
    const props = this.properties[frame];
    if (!props) {
      return;
    }
    const { t } = props;
    this.cursor = Math.max(0, Math.min(this.cursor, props.t.length));
    this.cursor_selection = Math.max(0, Math.min(this.cursor_selection, props.t.length));
  };

  this.char_index_at_x = function (x) {
    const props = this.properties[frame];
    if (!props) {
      return 0;
    }

    const idx = Math.round((x - props.p.x) / charSize);
    return Math.max(0, Math.min(idx, props.t.length));
  };

  this.duplicate = function () {
    if (!this.selected) {
      return;
    }

    const newc = new Text(this.text, null);
    newc.properties[frame] = copy(this.properties[frame]);
    newc.selected = true;
    this.selected = false;
    objs.push(newc);
  };

  this.copy_properties = function (f, n) {
    this.properties[n] = copy(this.properties[f]);
  };

  this.set_color = function (rgba) {
    if (this.selected) {
      rgba[3] = this.properties[frame].c[3];
      this.properties[frame].c = rgba;
    }
  };

  this.hide = function () {
    if (this.selected) {
      if (this.properties[frame].c[3] === 1) {
        this.properties[frame].c[3] = 0;
      } else {
        this.properties[frame].c[3] = 1;
      }

      this.selected = false;
    }
  };

  this.clear_props = function (f) {
    delete this.properties[f];
  };

  this.clear_all_props = function () {
    if (!this.selected) {
      return;
    }

    for (const key in this.properties) {
      if (key !== frame) {
        delete this.properties[key];
      }
    }
  };

  this.del_props_before = function () {
    if (!this.selected) {
      return;
    }

    if (this.properties && this.properties[frame - 1]) {
      delete this.properties[frame - 1];
    }
  };

  this.hidden = function () {
    if (!this.properties[frame]) {
      return true;
    }

    if (transition.transitioning) {
      return this.properties[frame].c[3] === 0 && this.properties[nextFrame].c[3] === 0;
    }

    return this.properties[frame].c[3] === 0;
  };

  this.in_rect = function (x, y, x2, y2) {
    if (this.hidden()) {
      return false;
    }

    const props = this.properties[frame];
    let p;
    if (props.ge) {
      p = { x: props.p.x + cam.props.p.x, y: props.p.y + cam.props.p.y };
    } else {
      p = props.p;
    }

    if (p.x > x && p.y > y && p.x < x2 && p.y < y2) {
      this.select();
      return true;
    }

    return false;
  };

  this.split = function () {
    if (!this.is_selected()) {
      return;
    }

    const { t } = this.properties[frame];

    if (t.indexOf('visnet') !== -1) {
      // very hacky but it works.. :-)

      const { p } = this.properties[frame];

      const l = math.eval(t.substring(t.indexOf('['), t.indexOf(']') + 1));

      drawNetwork(l._data, [p.x, p.y]);

      // hide
      this.properties[frame].c[3] = 0;
      this.selected = false;

      return;
    }

    // for each character, make it it's own text obj
    if (!t) {
      return;
    }

    const { p } = this.properties[frame];

    // if its a matrix split that up too
    if (this.matrix_vals.length !== 0) {
      // create a bunch of matrix numbers
      const pad = 24;

      const maxWidth = matNumWidth - 20;

      const matrix = formatMatrix(this.matrix_vals);

      for (let i = 0; i < matrix.length; i++) {
        for (let j = 0; j < matrix[i].length; j++) {
          const newT = new Text(matrix[i][j], {
            x: p.x + j * (matNumWidth + pad) + 110,
            y: p.y + i * gridSize,
          });
          objs.push(newT);
        }
      }

      const size = matrixSize(matrix);
      drawBrackets(0, 0, size[0], size[1]);

      return;
    }

    const N = t.length;
    let xoff = 0;
    for (let i = 0; i < N; i++) {
      const c = t[i];
      if (c === ' ') {
        xoff += gridSize / 2;
        continue;
      }
      const newT = new Text(c, { x: p.x + xoff, y: p.y });
      objs.push(newT);
      xoff += gridSize / 2;
    }

    this.deleted = true;
  };

  this.onkeydown = function (evt) {
    if (!this.selected) {
      return false;
    }

    const { key } = evt;
    let text = this.properties[frame].t;

    if (ctrl) {
      this.properties[frame] = transformProps(key, this.properties[frame]);
      return true;
    }

    if (meta || ctrl) {
      if (this.is_selected()) {
        if (key === 'c') {
          // copy
          textCopied = this.text_selected();

          // hacky but works
          const el = document.createElement('textarea');
          el.value = this.text_selected();
          document.body.appendChild(el);
          el.select();
          document.execCommand('copy');
          document.body.removeChild(el);

          return true;
        } if (key === 'v') {
          // paste, let event take over
          return false;
        } if (key === 'a') {
          // select all
          this.cursor = this.properties[frame].t.length;
          this.cursor_selection = 0;
          return true;
        }
      }

      return true;
    }

    if (tab) {
      // auto complete
      const fn = text.split(/[^A-Za-z]/).pop();

      if (fn.length !== 0) {
        const keys = Object.keys(math);

        for (let i = 0; i < keys.length; i++) {
          const key = keys[i];

          if (key.indexOf(fn) === 0) {
            let newText = text.split(fn)[0] + keys[i];
            if ((`${math[key]}`).split('\n')[0].indexOf('(') !== -1) {
              newText += '(';
            }

            this.change_text(newText);
            this.cursor = newText.length;
            this.cursor_selection = this.cursor;
            break;
          }
        }
      }

      return true;
    }

    if (key === 'Escape') {
      this.selected = false;
      return false;
    }

    if (key === 'Enter') {
      this.selected = false;
      this.eval();
      if (shift) {
        // create a new text below this one
        const { p } = this.properties[frame];
        const newT = new Text('', { x: p.x, y: p.y + charSize * 2 });
        objs.push(newT);
        newT.select();
        saveState();
      } else {
        enterSelect();
      }

      return false;
    }

    if (!shift && this.is_text_selected()) {
      const s = this.selection_indices();
      if (key === 'ArrowRight') {
        this.cursor = s.e;
      } else if (key === 'ArrowLeft') {
        this.cursor = s.s;
      }
    } else if (key === 'ArrowRight') {
      this.cursor += 1;
    } else if (key === 'ArrowLeft') {
      this.cursor -= 1;
    }

    if (key === 'ArrowUp') {
      // find text above
      const texts = objs.filter((o) => o.type === 'Text');

      texts.sort((a, b) => {
        const ap = a.properties[frame].p;
        const bp = b.properties[frame].p;
        return ap.y > bp.y;
      });

      const i = guidIndex(texts, this);
      if (i === 0) {
        return true;
      }

      const newObj = texts[i - 1];
      newObj.selected = true;
      this.selected = false;
      return true;
    } if (key === 'ArrowDown') {
      // find text below
      const texts = objs.filter((o) => o.type === 'Text');

      texts.sort((a, b) => {
        const ap = a.properties[frame].p;
        const bp = b.properties[frame].p;
        return ap.y > bp.y;
      });

      const i = guidIndex(texts, this);
      if (i === texts.length - 1) {
        return true;
      }

      const newObj = texts[i + 1];
      newObj.selected = true;
      this.selected = false;
      return true;
    }

    if (key === 'Backspace') {
      if (!this.is_text_selected()) {
        this.cursor_selection = this.cursor - 1;
        this.constrain_cursors();
        text = this.replace_selected_text('');
      } else {
        text = this.replace_selected_text('');
      }
    } else if (key.length === 1) {
      // type character
      if (this.is_text_selected()) {
        text = this.replace_selected_text(key);
      } else {
        text = text.slice(0, this.cursor) + key + text.slice(this.cursor, text.length);
        this.cursor += 1;
      }
    }

    if (!shift || (key !== 'ArrowRight' && key !== 'ArrowLeft')) {
      this.cursor_selection = this.cursor;
    }

    this.change_text(text);

    return true;
  };

  this.eval = function () {
    if ((!presenting && this.is_selected()) || this.hidden()) {
      return;
    }

    this.text_val = '';
    this.matrix_vals = [];
    const expr = '';

    if (this.new) {
      this.new = false;
      this.parse_text(this.properties[frame].t);
    }

    if (!this.cargs[0]) {
      return;
    }

    ctx.save();

    const a = this.properties[frame];
    const b = this.properties[nextFrame];

    let i;
    if (transition.transitioning) {
      i = interpolate(a, b);
    } else {
      i = a;
    }

    const color = rgbToHex(i.c);

    ctx.strokeStyle = color;
    ctx.fillStyle = color;
    ctx.globalAlpha = i.c[3];

    if (transition.transitioning) {
      if (a.t !== b.t) {
        // text is diff, cross fade result
        // ctx.globalAlpha = -math.cos(t_percent*2*math.PI-math.PI)/2 + .5;
        /*
                if (t_percent > .5) {
                    this.parse_text(this.properties[next_frame].t);
                } */
      }
    }

    try {
      parser.set('text_props', i);

      const val = this.cargs[0].eval(parser.scope);

      // only display the value if its not an assignment or constant
      const opType = math.parse(this.args[0]).type;

      if (opType.indexOf('Assignment') === -1 && opType !== 'ConstantNode') {
        const type = typeof val;

        // set display text
        if (type === 'number') {
          if (ctrl) {
            // nothing
            this.text_val = `=${val}`;
          } else {
            this.text_val = `=${prettyRound(val)}`;
          }
        } else if (type === 'boolean') {
          this.text_val = ` = ${val}`;
        } else if (type === 'object' && val._data && val._data.length !== 0) {
          // prob a matrix, render entries
          this.matrix_vals = val._data;
          this.text_val = null;
        } else if (val && 're' in val && val.im) {
          if (val) {
            if (ctrl) {
              // nothing
              this.text_val = `=${val}`;
            } else {
              this.text_val = `=${prettyRound(val.re).toString()} + ${prettyRound(val.im).toString()}i`;
            }
          }
        } else if (val) {
          this.text_val = `=${val.toString()}`;
        }
      }
    } catch (e) {
      console.log('eval error:');
      console.log(e);
    }

    ctx.restore();
  };

  this.change_text = function (text) {
    const changed = this.properties[frame].t !== text;

    this.properties[frame].t = text;
    this.constrain_cursors();

    if (changed) {
      this.parse_text(text);
    }
  };

  this.mouse_down = function (evt) {
    if (this.hidden()) {
      return false;
    }

    this.near_mouse = this.point_in_text_rect(mouse);

    if (this.near_mouse) {
      return true;
    }

    return false;
  };

  this.point_in_text_rect = function (point) {
    const props = this.properties[frame];
    if (!props) {
      return false;
    }

    const { p } = props;

    if (this.image) {
      const w = this.image.width * props.w;
      const h = this.image.height * props.h;
      if (point.x > p.x - w / 2 && point.x < p.x + w / 2 && point.y > p.y - h / 2 && point.y < p.y + h / 2) {
        return true;
      }
    } else if (point.x > p.x && point.x < p.x + this.size.w && point.y > p.y - this.size.h / 2 && point.y < p.y + this.size.h / 2) {
      return true;
    }

    return false;
  };

  this.mouse_move = function (evt) {
    const props = this.properties[frame];
    if (!props) {
      return;
    }

    this.near_mouse = this.point_in_text_rect(mouse);
  };

  this.var_name = function () {
    let varName = this.args[0].split('=')[0];
    varName = varName.replace(/\s+/g, '');
    return varName;
  };

  this.mouse_drag = function (evt) {
    if (tool === 'camera') {
      return false;
    }

    const props = this.properties[frame];
    if (!props) {
      return false;
    }

    if (Math.abs(mouse.x - mouseStart.x) > charSize || Math.abs(mouse.y - mouseStart.y) > charSize) {
      this.dragged = true;
    }

    if (presenting) {
      if (this.args && this.args[0] && this.args[0]._data) {

      } else if (this.command === 'slide' && this.point_in_text_rect(mouseStart)) {
        // change the value of the variable
        const varName = this.var_name();

        let oldVal = 0;
        try {
          oldVal = parser.eval(varName);
        } catch (e) {

        }

        if (isNaN(oldVal)) {
          oldVal = 0;
        }

        let delta = (mouse.x - mouseLast.x) / gridSize;
        if (meta || ctrl) {
          delta *= 0.01;
        }

        const newVal = oldVal + delta;
        this.text_val = `=${prettyRound(newVal)}`;

        try {
          parser.set(varName, newVal);
        } catch (error) {
          console.log(`slide error: ${error}`);
        }

        return true;
      }
    } else if (this.is_selected() && this.near_mouse && this.image == null) {
      const { p } = props;

      this.cursor = this.char_index_at_x(mouse.x);
      this.cursor_selection = this.char_index_at_x(mouseStart.x);

      this.constrain_cursors();
      this.dragged = true;
    } else if (tool === 'select' && (this.near_mouse || this.is_selected())) {
      // shift it
      const { p } = props;
      const offset = { x: mouseGrid.x - mouseGridLast.x, y: mouseGrid.y - mouseGridLast.y };
      props.p = { x: p.x + offset.x, y: p.y + offset.y };

      return true;
    }

    return false;
  };

  this.mouse_up = function (evt) {
    if (this.hidden()) {
      return false;
    }

    if (this.near_mouse) {
      if (!this.dragged) {
        this.select();

        // move cursor
        this.cursor = this.char_index_at_x(mouse.x);
        this.cursor_selection = this.cursor;
        this.constrain_cursors();
        return true;
      }
    } else if (!shift && this.is_selected()) {
      this.selected = false;
    }

    this.dragged = false;
    return false;
  };

  this.draw_text = function (ctx, t) {
    let size;

    if (this.command === 'f' && !this.is_selected()) {
      const fn = t.slice(this.command.length + 1); // +1 for semicolon
      size = drawFn(fn);
    } else {
      const N = t.length;
      size = { w: N * charSize, h: charSize * 2 };

      size = { w: drawSimple(t), h: charSize * 2 };

      let plevel = 0;
      for (let i = 0; i < N; i++) {
        if (i < this.cursor) {
          if (t[i] in brackets) plevel += brackets[t[i]];
        }
      }

      // draw red brackets
      ctx.save();
      if (this.is_selected() && plevel !== 0) {
        ctx.fillStyle = colors[1];
        let p2 = plevel;
        for (let i = this.cursor; i < N; i++) {
          if (t[i] in brackets) p2 += brackets[t[i]];

          if (p2 === plevel - 1) {
            ctx.fillText(t[i], i * charSize, 0);
            break;
          }
        }

        p2 = plevel;
        for (let i = this.cursor - 1; i >= 0; i--) {
          if (t[i] in brackets) p2 += brackets[t[i]];

          if (p2 === plevel + 1) {
            ctx.fillText(t[i], i * charSize, 0);
            break;
          }
        }
      }
      ctx.restore();
    }

    if (this.matrix_vals.length !== 0) {
      ctx.save();
      ctx.translate(size.w, 0);
      ctx.fillText('=', 0, 0);
      ctx.translate(135, 0);

      ctx.translate(-100, -20);
      const formatted = formatMatrix(this.matrix_vals);
      drawMatrix(formatted);

      ctx.restore();
    } else if (!this.selected && this.text_val && this.text_val.length) {
      ctx.save();
      ctx.translate(size.w, 0);
      size.w += drawSimple(this.text_val);
      ctx.restore();
    }

    return size;
  };

  this.parse_text = function (text) {
    this.command = '';
    this.args = [];
    this.cargs = [];

    // replace @ with anonymous fn name
    if (text && text.length) {
      const split = text.split('@');
      let newT = '';
      const N = split.length;
      for (let i = 0; i < N - 1; i++) {
        newT += `${split[i]}anon${guid().slice(0, 8)}`;
      }
      newT += split[N - 1];
      text = newT;
    }

    if (!text) {

    } else if (text.indexOf(':') !== -1) {
      const split = text.split(':');
      this.command = split[0];
      this.args = [split[1]];

      try {
        this.cargs = math.compile(this.args);
      } catch (e) {
        // report_error(e);
      }
    } else {
      this.args = [text];

      try {
        this.cargs = math.compile(this.args);
      } catch (e) {
        console.log('compile2 error: ');
        console.log(e);
      }
    }
  };

  this.draw_tree = function (ctx, props) {
    ctx.save();

    if (this.args.length !== 1) {
      return;
    }

    let t = -1;

    try {
      t = math.parse(this.args[0]);
    } catch (e) {

    }

    if (t === -1) {
      return;
    }

    const yoff = gridSize * 3;
    const xoff = gridSize * 3;
    const opSize = gridSize;

    const p = { x: props.p.x, y: props.p.y + gridSize };
    let stuff = [t];

    if (!stuff) {
      return;
    }

    while (true) {
      let nextStuff = [];
      let addedAllSpaces = true;
      for (let i = 0; i < stuff.length; i++) {
        const o = stuff[i];
        if (o.args) {
          nextStuff = nextStuff.concat(o.args);
          addedAllSpaces = false;
        } else {
          nextStuff.push(' ');
        }
      }

      let lx = -(nextStuff.length - 1) / 2 * xoff;
      let li = 0;

      for (let i = 0; i < stuff.length; i++) {
        const o = stuff[i];
        if (o === ' ') {
          continue;
        }

        let text;
        const np = { x: p.x + i * xoff - (stuff.length - 1) / 2 * xoff, y: p.y };

        if (o.args) {
          // draw the op name

          if (o.name && o.name.length) {
            text = o.name;
          } else if (o.op && o.op.length) {
            text = o.op;
          }

          if (distance(mouse, np) < gridSize) {
            text = o.toString();
          }

          /* ctx.beginPath();
                    ctx.arc(np.x, np.y, op_size, 0, pi2);
                    ctx.stroke(); */

          ctx.fillText(text, np.x, np.y);

          for (let j = 0; j < o.args.length; j++) {
            while (nextStuff[li] === ' ') {
              lx += xoff;
              li += 1;
            }

            const argp = { x: p.x + lx, y: np.y + yoff };
            let diff = { x: argp.x - np.x, y: argp.y - np.y };
            const n = math.norm([diff.x, diff.y]);
            diff = { x: diff.x / n, y: diff.y / n };

            ctx.beginPath();
            ctx.moveTo(np.x + diff.x * opSize, np.y + diff.y * opSize);
            ctx.lineTo(argp.x - diff.x * opSize, argp.y - diff.y * opSize);
            ctx.stroke();

            lx += xoff;
            li += 1;
          }
        } else {
          if (o.name && o.name.length) {
            text = o.name;
          } else if (o.items) {
            text = 'A'; // array
          } else if (o.value) {
            text = o.value;
          } else if (o.content) {
            text = o.content;
          } else {
            text = '?';
          }

          ctx.fillText(text, np.x, np.y);
        }
      }

      if (nextStuff.length === 0) {
        break;
      }

      if (addedAllSpaces) {
        break;
      }

      stuff = nextStuff;
      p.y += yoff;
    }

    ctx.restore();
  };

  this.draw_border = function (ctx) {
    ctx.save();
    ctx.fillStyle = gray;
    ctx.globalAlpha = 0.2;

    if (this.image) {
      ctx.strokeRect(-this.image.width / 2, -this.image.height / 2, this.image.width, this.image.height);
    } else {
      ctx.strokeRect(0, -this.size.h / 2, this.size.w, this.size.h);
    }

    ctx.globalAlpha = 1.0;
    ctx.restore();
  };

  this.render = function (ctx) {
    const a = this.properties[frame];

    if (!a) {
      return;
    }

    let b = this.properties[nextFrame];

    let i;
    if (transition.transitioning) {
      i = interpolate(a, b);
    } else {
      i = a;
    }

    if (i.c[3] === 0) {
      return;
    }

    let pos = i.p;

    if (b && b.c[3] > a.c[3]) {
      // fade in, use final position always
      pos = b.p;
    } else if (b && b.c[3] < a.c[3]) {
      // fade out, use initial position
      pos = a.p;
    }

    ctx.save();

    ctx.globalAlpha = i.c[3];
    ctx.fillStyle = rgbToHex(i.c);
    ctx.strokeStyle = rgbToHex(i.c);

    let shouldDrawText = true;

    const c = this.command;
    if (c === 'tree') {
      this.draw_tree(ctx, i);
      if (presenting) {
        shouldDrawText = false;
      }
    }

    if (presenting && (a.ph || (b && b.ph))) {
      shouldDrawText = false;
    }

    // text
    this.size = { w: 0, h: 0 };

    ctx.translate(pos.x, pos.y);
    ctx.rotate(i.r);
    ctx.scale(i.w, i.h);

    // image display
    if (i.t.indexOf('http') !== -1 && (i.t.indexOf('png') !== -1 || i.t.indexOf('jpg') !== -1 || i.t.indexOf('gif') !== -1 || i.t.indexOf('jpeg') !== -1)) {
      if (this.image === null || this.image.src !== i.t) {
        this.image = new Image();
        this.image.src = i.t;
      } else {
        ctx.drawImage(this.image, -this.image.width / 2, -this.image.height / 2);
        this.size = { w: this.image.width * i.w, h: this.image.height * i.h };
      }
    } else if (shouldDrawText) {
      if (!b) {
        b = a;
      }

      const fadingIn = (a.c[3] === 0 && b.c[3] === 1);
      const fadingOut = (a.c[3] === 1 && b.c[3] === 0);

      let at = a.t;
      let bt = b.t;

      if (transition.transitioning) {
        if (fadingIn) {
          at = b.t;
          bt = b.t;
        } else if (fadingOut) {
          at = a.t;
          bt = a.t;
        }
      }

      const textDifferent = at !== bt;

      if (textDifferent && transition.transitioning) {
        // changing text
        const constrained = constrain(tEase);
        ctx.globalAlpha = 1 - constrained;
        this.draw_text(ctx, a.t);
        ctx.globalAlpha = constrained;
        this.draw_text(ctx, b.t);
      } else {
        ctx.globalAlpha = i.c[3];
        this.size = this.draw_text(ctx, at);
      }
    }

    if (c === 'slide' && presenting && this.near_mouse && !this.hidden()) {
      // draw slider rect
      this.draw_border(ctx);
    }

    if (!presenting && !this.hidden() && this.near_mouse) {
      // draw border
      this.draw_border(ctx);
    }

    if (!presenting && this.is_selected()) {
      // draw cursor
      ctx.fillRect(this.cursor * charSize, -gridSize / 2, 2, gridSize);
      if (this.is_text_selected()) {
        // draw selection
        const s = this.selection_indices();

        const xstart = s.s * charSize;
        const xend = s.e * charSize;

        ctx.save();
        ctx.globalAlpha = 0.1;
        ctx.fillRect(xstart, -gridSize / 2, xend - xstart, gridSize);
        ctx.restore();
      }

      // draw function information
      if (i.t) {
        text = i.t.slice(0, this.cursor);
        const fn = text.split(/[^A-Za-z]/).pop();

        if (fn.length !== 0) {
          const keys = Object.keys(math);
          let yoff = 0;

          for (let i = 0; i < keys.length; i++) {
            const key = keys[i];

            if (key.indexOf(fn) === 0) {
              ctx.save();
              ctx.translate(0, charSize * 2 + yoff);
              ctx.scale(0.5, 0.5);
              ctx.globalAlpha = 0.5;
              drawSimple(`${key}: ${(`${math[key]}`).split('\n')[0]}`);
              ctx.restore();
              yoff += gridSize;
            }
          }
        }
      }
    }

    ctx.restore();
  };

  this.generate_javascript = function () {
    const props = this.properties[frame];
    const { p } = props;
    const cp = cam.properties[frame].p;
    const text = props.t;

    let js = '';
    js += 'ctx.save();\n';
    js += `ctx.translate(x + ${p.x - cp.x}, y + ${p.y - cp.y});\n`;
    js += `ctx.rotate(${props.r});\n`;
    js += `ctx.scale(${props.w}, ${props.h});\n`;
    js += `ctx.fillStyle = "${rgbToHex(props.c)}";\n`;

    for (let i = 0; i < text.length; i++) {
      if (text[i] === '*') {
        js += 'ctx.beginPath();\n';
        js += `ctx.arc(${i * charSize + charSize / 2}, 0, 3, 0, ${pi2});\n`;
        js += 'ctx.fill();\n';
      } else {
        js += `ctx.fillText("${text[i]}", ${i * charSize}, 0);\n`;
      }
    }

    js += 'ctx.restore();\n';

    return js;
  };

  this.parse_text(text);
}

function Network(pos) {
  this.type = 'Network';
  this.guid = guid();
  this.properties = {};
  this.properties[frame] = {
    layers: [2, 3, 2], p: pos, c: [0, 0, 0, 1], w: 1, h: 1, r: 0,
  };

  // ephemeral
  this.new = true; // loaded or just created
  this.selected = false;
  this.dragged = false;

  this.select = function () {
    this.selected = true;
  };

  this.is_selected = function () {
    return this.selected;
  };

  this.hidden = function () {
    if (!this.properties[frame]) {
      return true;
    }

    return this.properties[frame].c[3] === 0;
  };

  this.copy_properties = function (f, n) {
    this.properties[n] = copy(this.properties[f]);
  };

  this.duplicate = function () {
    if (!this.selected) {
      return;
    }

    const newc = new Network(null);
    newc.properties[frame] = copy(this.properties[frame]);
    newc.selected = true;
    this.selected = false;
    objs.push(newc);
  };

  this.hide = function () {
    if (this.selected) {
      if (this.properties[frame].c[3] === 1) {
        this.properties[frame].c[3] = 0;
      } else {
        this.properties[frame].c[3] = 1;
      }
      this.selected = false;
    }
  };

  this.set_color = function (rgba) {
    if (this.selected) {
      rgba[3] = this.properties[frame].c[3];
      this.properties[frame].c = rgba;
    }
  };

  this.clear_props = function (f) {
    delete this.properties[f];
  };

  this.clear_all_props = function () {
    if (!this.selected) {
      return;
    }

    for (const key in this.properties) {
      if (key !== frame) {
        delete this.properties[key];
      }
    }
  };

  this.del_props_before = function () {
    if (!this.selected) {
      return;
    }

    if (this.properties && this.properties[frame - 1]) {
      delete this.properties[frame - 1];
    }
  };

  this.near_mouse = function () {
    const props = this.properties[frame];
    if (!props) {
      return false;
    }

    return distance(props.p, mouse) < gridSize / 2;
  };

  this.in_rect = function (x, y, x2, y2) {
    if (this.hidden()) {
      return false;
    }

    const props = this.properties[frame];
    const { p } = props;

    if (p.x > x && p.x < x2 && p.y > y && p.y < y2) {
      this.selected = true;
      return true;
    }

    return false;
  };

  this.mouse_down = function (evt) {
    if (this.hidden()) {
      return false;
    }

    // try to selected one
    if (this.near_mouse()) {
      this.selected = true;
      return true;
    }

    return false;
  };

  this.mouse_drag = function (evt) {
    if (this.selected && tool === 'select') {
      // move
      const props = this.properties[frame];
      const offset = {
        x: mouseGrid.x - mouseGridLast.x,
        y: mouseGrid.y - mouseGridLast.y,
      };
      const { p } = props;
      this.properties[frame].p = { x: p.x + offset.x, y: p.y + offset.y };
    }
  };

  this.mouse_up = function (evt) {
    if (!shift) {
      this.selected = false;
    }
  };

  this.draw_network = function (props, ctx) {
    const { p } = props;
    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(props.r);
    ctx.scale(props.w, props.h);

    layers = props.layers;

    const pad = 120;

    const pos = [0, 0];

    const radius = 14;

    loc = function (i, j, units) {
      const pad2 = 250;
      // return [pos[0] - pad2/2 - j*(pad2+80), pos[1] + pad2/2 - pad2 * units/2 + i*pad2];
      return [pos[0] - pad2 * units / 2 + pad2 / 2 + i * pad2, -pad + pos[1] - j * pad2];
    };

    // connections
    let highConn = [];
    let highNeur = [];

    for (let j = 0; j < layers.length - 1; j++) {
      const units = layers[j];
      const unitsNext = layers[j + 1];

      for (let i = 0; i < units; i++) {
        const p = loc(i, j, units);

        for (let k = 0; k < unitsNext; k++) {
          const p2 = loc(k, j + 1, unitsNext);

          /*
                    let vline = [p2[0] - p[0], p2[1] - p[1]];
                    let mvect = [mouse.x - p[0], mouse.y - p[1]];

                    let dot = mvect[0] * vline[0] + mvect[1] * vline[1];

                    let vlen = math.norm(vline);
                    let total_len = vlen * math.norm(mvect);

                    if (dot > total_len * .998 && dot < vlen*vlen) {
                        ctx.strokeStyle = "red";
                    } else {
                        ctx.strokeStyle = "black";
                    } */

          ctx.strokeStyle = 'black';

          if (highConn.length === 0) {
            const dx1 = p[0] - mouse.x;
            const dy1 = p[1] - mouse.y;

            const dx2 = p2[0] - mouse.x;
            const dy2 = p2[1] - mouse.y;

            const d1 = math.sqrt(dx1 * dx1 + dy1 * dy1);
            const d2 = math.sqrt(dx2 * dx2 + dy2 * dy2);

            const vline = [p2[0] - p[0], p2[1] - p[1]];
            const vlen = math.norm(vline);

            if (d1 + d2 < vlen + 1) {
              ctx.strokeStyle = 'green';
              highConn = [i, k, j]; // unit i to unit k in layer j
              highNeur = [[i, j], [k, j + 1]];
            }
          }

          ctx.beginPath();
          ctx.moveTo(p[0], p[1]);
          ctx.lineTo(p2[0], p2[1]);
          ctx.stroke();
        }
      }
    }

    ctx.fillStyle = 'white';

    // neurons
    for (let j = 0; j < layers.length; j++) {
      const units = layers[j];

      for (let i = 0; i < units; i++) {
        const p = loc(i, j, units);

        ctx.strokeStyle = 'black';

        // if we have a highlighted connection and we're in the right layer
        if (highConn.length !== 0) {
          if (highConn[2] === j) {
            if (highConn[0] === i) {
              if (j === 0) {
                ctx.strokeStyle = 'blue';
              } else {
                ctx.strokeStyle = 'red';
              }
            }
          } else if (highConn[2] === j - 1) {
            if (highConn[1] === i) {
              if (j === 0) {
                ctx.strokeStyle = 'blue';
              } else {
                ctx.strokeStyle = 'red';
              }
            }
          }
        } else {
          const dx = mouse.x - p[0];
          const dy = mouse.y - p[1];

          if (dx * dx + dy * dy < 400) {
            if (j === 0) {
              ctx.strokeStyle = 'blue';
            } else {
              ctx.strokeStyle = 'red';
            }

            highNeur = [[i, j]];
          }
        }

        ctx.beginPath();
        ctx.arc(p[0], p[1], radius, 0, 2 * Math.PI);
        ctx.fill();
        ctx.stroke();
      }
    }

    ctx.restore();
  };

  this.render = function (ctx) {
    const a = this.properties[frame];
    const b = this.properties[nextFrame];

    if (!a) {
      return;
    }

    let props;
    if (transition.transitioning) {
      props = interpolate(a, b);
    } else {
      props = a;
    }

    ctx.beginPath();
    this.draw_network(props, ctx);

    if (!presenting && props.c[3] !== 0 && (this.selected || this.near_mouse())) {
      ctx.beginPath();
      ctx.strokeStyle = dark;
      ctx.strokeRect(props.p.x - gridSize / 4, props.p.y - gridSize / 4, gridSize / 2, gridSize / 2);
      ctx.stroke();
    }
  };
}

function Camera() {
  this.default_props = {
    p: { x: c.width / 2, y: c.height / 2 }, w: 1, h: 1, rxyz: [0, 0, 0], style: '3d',
  };
  this.properties = {};
  this.properties[frame] = copy(this.default_props);
  this.dragging_rotate = false;

  function generateTicks() {
    const ticks = [];

    const R = math.range(-10, 11, 1);
    const N = R.size()[0];
    const m = [];
    const tickSize = 10;

    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < N; j++) {
        const t = R._data[j];
        if (i === 0) {
          m.push([t, -tickSize, 0]);
          m.push([t, tickSize, 0]);
        } else if (i === 1) {
          // y axis
          m.push([-tickSize, t, 0]);
          m.push([tickSize, t, 0]);
        } else if (i === 2) {
          // z axis
          m.push([-tickSize, 0, t]);
          m.push([tickSize, 0, t]);
        }
      }

      ticks.push(m);
    }

    return ticks;
  }

  this.ticks = generateTicks();

  this.style = function () {
    const props = this.properties[frame];
    if (props) {
      return props.style;
    }

    return null;
  };

  this.set_style = function (style) {
    const props = this.properties[frame];
    if (props) {
      props.style = style;
      return true;
    }

    return false;
  };

  this.mouse_down = function (evt) {
    if (meta || ctrl) {
      const props = this.properties[frame];
      if (!props) {
        return false;
      }

      const dx = mouse.x - props.p.x;
      const dy = mouse.y - props.p.y;

      const dist = dx * dx + dy * dy;
      this.dragging_rotate = dist > 100000;

      return true;
    }

    return false;
  };

  this.mouse_drag = function (evt) {
    if (tool !== 'camera') {
      return;
    }

    const props = this.properties[frame];

    if (meta || ctrl) {
      // rotate
      let r = props.rxyz;

      if (!this.dragging_rotate) {
        a = r[1] - (mouse.y - mouseLast.y) / 100;
        b = r[2] - (mouse.x - mouseLast.x) / 100;
        r = [r[0], a, b];
      } else {
        const angle = math.atan2(mouse.y - props.p.y, mouse.x - props.p.x);
        const angle2 = math.atan2(mouseLast.y - props.p.y, mouseLast.x - props.p.x);
        let c = (angle - angle2);

        if (Math.abs(c) > 1) {
          c = 0;
        }

        c += r[0];

        r = [c, r[1], r[2]];
      }

      this.rotate(r);
    } else {
      // translate
      const { p } = props;
      const offset = { x: mouseGrid.x - mouseGridLast.x, y: mouseGrid.y - mouseGridLast.y };
      props.p = { x: p.x + offset.x, y: p.y + offset.y };
    }
  };

  this.rotate = function (rxyz) {
    const props = this.properties[frame];
    if (props) {
      props.rxyz = rxyz;
    }
  };

  this.onkeydown = function (evt) {
    if (tool !== 'camera') {
      return;
    }

    const { key } = evt;
    this.properties[frame] = transformProps(key, this.properties[frame], 0.01);
  };

  this.update_props = function () {
    const a = this.properties[frame];
    const b = this.properties[nextFrame];

    if (!a) {
      this.properties[frame] = copy(this.default_props);
      this.props = this.properties[frame];
      return;
    }

    if (a && !b) {
      this.properties[nextFrame] = copy(a);
      this.props = a;
      return;
    }

    if (transition.transitioning) {
      this.props = interpolate(a, b);
    } else {
      this.props = a;
    }

    if (!this.props.rxyz) {
      this.props.rxyz = [0, 0, 0];
    }

    const rx = this.props.rxyz[0];
    const ry = this.props.rxyz[1];
    const rz = this.props.rxyz[2];

    this.R = rotationMatrix(rx, ry, rz);
  };

  this.graph_to_screen = function (x, y, z) {
    // takes array [x, y, z]
    // returns [x, y, z] projected to screen (render using first two coords)
    return this.graph_to_screen_mat(math.matrix([[x, y, z]]))[0];
  };

  this.graph_to_screen_mat = function (p) {
    // n x ?
    const size = p.size();
    const n = size[0];
    const d = size[1];

    if (d === 2) {
      // 2d
      // append zeros for zs
      p = p.resize([n, 3]);
    }

    p = math.multiply(p, this.R);
    p = p._data;

    let x; let y; let z; let m;
    for (let i = 0; i < n; i++) {
      x = p[i][1];
      y = p[i][2];
      z = p[i][0];

      /*
            m = z/20+1;
            if (m < 0) {
                m = 1;
            } */

      p[i][0] = x * this.props.w * gridSize + this.props.p.x;
      p[i][1] = -y * this.props.h * gridSize + this.props.p.y;
      p[i][2] = z;
    }

    return p;
  };

  this.screen_to_graph = function (p) {
    return { x: (p.x - this.props.p.x) / (gridSize * this.props.w), y: -(p.y - this.props.p.y) / (gridSize * this.props.h) };
  };

  this.update_props();
}

function saveState() {
  // save state
  const str = stateToString();
  if (states.length > 0) {
    const last = states[states.length - 1];
    if (str !== last) {
      states.push(str);
    }
  } else {
    states = [str];
  }
}

function undo() {
  if (states.length > 1) {
    states = states.splice(0, states.length - 1);
    stringToState(states[states.length - 1]);
  }
}

function guidIndex(objs, obj) {
  const N = objs.length;
  for (let i = 0; i < N; i++) {
    const tobj = objs[i];
    if (tobj.guid === obj.guid) {
      return i;
    }
  }

  return -1;
}

function stateToString() {
  return JSON.stringify({
    num_frames: numFrames, frame, objs, cam, pen,
  });
}

function stringToState(str) {
  const dict = JSON.parse(str);
  const arr = dict.objs;

  if (dict.num_frames) {
    numFrames = dict.num_frames;
  }

  if (dict.frame) {
    frame = dict.frame;
    frames.create_buttons();
  }

  if (dict.pen) {
    pen = new Pen();
    pen.drawings = dict.pen.drawings;
  }

  if (dict.cam && dict.cam.properties) {
    cam = new Camera();
    cam.properties = dict.cam.properties;
    cam.update_props();
  }

  objs = textArrayToObjs(arr, true);
}

function save(objs) {
  const str = stateToString();
  const blob = new Blob([str], { type: 'text/plain;charset=utf-8' });
  const name = document.getElementById('name').value;
  saveAs(blob, name);
}

function load(evt) {
  const { files } = evt.target; // FileList object
  const f = files[0];

  const reader = new FileReader();

  // Closure to capture the file information.
  reader.onload = (function (theFile) {
    return function (e) {
      const string = e.target.result;
      stringToState(string);
    };
  }(f));

  reader.readAsText(f);
}

function saveLocal() {
  localStorage.setItem('page', stateToString());
}

function loadLocal() {
  // Grab the objects from storage
  const page = localStorage.getItem('page');
  if (page && page.length) {
    stringToState(page);
  }
}

function textArrayToObjs(arr, keepAnimation) {
  const newObjs = [];
  for (let i = 0; i < arr.length; i++) {
    const o = arr[i];
    let newObjs = null;

    if (o.type === 'Shape') {
      newObjs = new Shape();
    } else if (o.type === 'Circle') {
      newObjs = new Circle();
    } else if (o.type === 'Text') {
      newObjs = new Text();
    }

    if (keepAnimation) {
      newObjs.properties = o.properties;
    } else {
      newObjs.properties = {};
      newObjs.properties[frame] = o.properties[1];
      newObjs.select();
    }

    newObjs.guid = o.guid;

    newObjs.push(newObjs);
  }

  return newObjs;
}

function Frames(pos) {
  this.pos = pos;
  this.size = gridSize / 2;

  this.frame_pos = function (i) {
    const size = (this.size + gridSize / 4);
    let yoffset = (i - 1) * size;
    let xoff = 0;
    const hcon = size * 30;
    while (yoffset >= hcon) {
      yoffset -= hcon;
      xoff++;
    }
    return { x: this.pos.x + xoff * gridSize * 2 / 3, y: this.pos.y + yoffset + gridSize / 2 };
  };

  this.create_buttons = function () {
    this.buttons = [];
    for (let i = 1; i <= numFrames; i++) {
      const newb = new Button(`${i}`, this.frame_pos(i), null);
      this.buttons.push(newb);
    }
    this.buttons.push(new Button('-', this.frame_pos(numFrames + 1), null));
    this.buttons.push(new Button('+', this.frame_pos(numFrames + 2), null));
  };

  this.create_buttons();

  this.mouse_down = function (evt) {
    for (let i = 0; i < this.buttons.length; i++) {
      const btn = this.buttons[i];
      if (btn.hovering()) {
        return true;
      }
    }

    return false;
  };

  this.mouse_up = function (evt) {
    for (let i = 0; i < this.buttons.length; i++) {
      const btn = this.buttons[i];
      if (btn.mouse_up(evt)) {
        if (i === this.buttons.length - 2) {
          // remove frame

          // remove selected frame
          // copy properties from next frames
          // decrement number of frames
          if (numFrames === 1) {
            break;
          }

          for (let f = frame; f <= numFrames; f++) {
            for (let i = 0; i < objs.length; i++) {
              const obj = objs[i];
              if (typeof obj.copy_properties === 'function') {
                if (!obj.properties[f]) {
                  continue;
                }
                if (!obj.properties[f + 1]) {
                  continue;
                }
                obj.copy_properties(f + 1, f);
              }
            }

            if (cam.properties[f] && cam.properties[f + 1]) {
              cam.properties[f] = copy(cam.properties[f + 1]);
            }
          }

          numFrames -= 1;
          this.create_buttons();
          return true;
        } if (i === this.buttons.length - 1) {
          // add frame
          // copy to next from frame
          insertFrame();
          return true;
        }
        this.on_click(i + 1);
      }
    }
  };

  this.onkeydown = function (evt) {
    const { key } = evt;

    if (key === 'ArrowRight') {
      if (!presenting && frame + 1 > numFrames) {
        // create a new one
        insertFrame();
      }

      transitionWithNext(loopFrame(frame + 1));
      return true;
    } if (key === 'ArrowLeft') {
      transitionWithNext(loopFrame(frame - 1));
      return true;
    }

    if ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9].indexOf(Number(key)) !== -1) {
      if (!transition.transitioning) {
        transitionWithNext(Number(key));
        return true;
      }

      return false;
    }

    return false;
  };

  this.render = function (ctx) {
    for (let i = 1; i <= this.buttons.length; i++) {
      const btn = this.buttons[i - 1];
      btn.selected = false;
      if (btn.text === `${frame}`) {
        btn.selected = true;
      }
      btn.render(ctx);
    }
  };
}

function insertFrame() {
  numFrames += 1;
  for (let f = numFrames; f >= frame; f--) {
    for (let i = 0; i < objs.length; i++) {
      const obj = objs[i];
      if (typeof obj.copy_properties === 'function') {
        if (!obj.properties[f]) {
          continue;
        }
        obj.copy_properties(f, f + 1);
      }
    }

    if (cam.properties[f]) {
      cam.properties[f + 1] = copy(cam.properties[f]);
    }
  }
  frames.create_buttons();
}

function present() {
  tool = 'select';
  presenting = true;
  document.body.style.cursor = 'none';
  document.body.scrollTop = 0; // Scroll to top in Safari
  document.documentElement.scrollTop = 0; // Scroll to top in other browsers
  document.body.style.overflow = 'hidden'; // Disable and hide scrollbar
}

function Menu(pos) {
  this.pos = pos;
  this.buttons = [];

  this.buttons.push(new Button('select', { x: 0, y: 0 }, ((b) => {
    enterSelect();
  })));

  this.buttons.push(new Button('text', { x: 0, y: 0 }, ((b) => {
    tool = 'text';
  })));

  this.buttons.push(new Button('pen', { x: 0, y: 0 }, ((b) => {
    if (tool !== 'pen') {
      tool = 'pen';
    } else {
      pen.clear_drawing();
    }
  })));

  this.buttons.push(new Button('split', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.split === 'function') {
        obj.split();
      }
    }
  })));

  this.buttons.push(new Button('shape', { x: 0, y: 0 }, ((b) => {
    tool = 'shape';
  })));

  this.buttons.push(new Button('circle', { x: 0, y: 0 }, ((b) => {
    tool = 'circle';
  })));

  this.buttons.push(new Button('vector', { x: 0, y: 0 }, ((b) => {
    tool = 'vector';
  })));

  /*
    this.buttons.push(new Button("network", {x: 0, y: 0}, function(b) {
        tool = "network";
    })); */

  this.buttons.push(new Button('delete', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      if (objs[i].is_selected()) {
        objs[i].deleted = true;
      }
    }
  })));

  this.buttons.push(new Button('del props all', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.clear_all_props === 'function') {
        obj.clear_all_props();
      }
    }
  })));

  this.buttons.push(new Button('del props before', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.del_props_before === 'function') {
        obj.del_props_before();
      }
    }
  })));

  this.buttons.push(new Button('duplicate', { x: 0, y: 0 }, ((b) => {
    for (let i = objs.length - 1; i >= 0; i--) {
      const obj = objs[i];
      if (typeof obj.duplicate === 'function') {
        obj.duplicate();
      }
    }
  })));

  this.buttons.push(new Button('copy frame', { x: 0, y: 0 }, ((b) => {
    tool = 'copy frame';
  })));

  this.buttons.push(new Button('hide', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.hide === 'function') {
        obj.hide();
      }
    }
  })));

  this.buttons.push(new Button('pres. hide', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (obj.properties && obj.is_selected()) {
        obj.properties[frame].ph = true;
      }
    }
  })));

  this.buttons.push(new Button('pres. show', { x: 0, y: 0 }, ((b) => {
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (obj.properties && obj.is_selected()) {
        obj.properties[frame].ph = false;
      }
    }
  })));

  this.buttons.push(new Button('camera', { x: 0, y: 0 }, ((b) => {
    if (tool === 'camera') {
      // reset the camera rotation
      cam.properties[frame].rxyz = [0, 0, 0];
      cam.properties[frame].p = cam.default_props.p;
    }
    tool = 'camera';
  })));

  this.buttons.push(new Button('csys', { x: 0, y: 0 }, ((b) => {
    const csysStyle = cam.style();

    if (csysStyle == '3d') {
      cam.set_style('flat');
      cam.properties[frame].w = 1.5;
      cam.properties[frame].h = 1.5;
      cam.rotate([-Math.PI / 2, 0, -Math.PI / 2]);
    } else if (csysStyle == 'flat') {
      cam.set_style('none');
    } else if (csysStyle == 'none') {
      cam.set_style('3d');
      cam.properties[frame].w = 1;
      cam.properties[frame].h = 1;
    }
  })));

  this.buttons.push(new Button('view xy', { x: 0, y: 0 }, ((b) => {
    cam.rotate([-Math.PI / 2, 0, -Math.PI / 2]);
  })));

  this.buttons.push(new Button('frame', { x: 0, y: 0 }, ((b) => {
    viewFrame = !viewFrame;
  })));

  this.buttons.push(new Button('debug', { x: 0, y: 0 }, ((b) => {
    debug = !debug;
  })));

  this.buttons.push(new Button('present', { x: 0, y: 0 }, ((b) => {
    // show a cursor
    present();
  })));

  this.buttons.push(new Button('save local', { x: 0, y: 0 }, ((b) => {
    // Put the object into storage
    saveLocal();
  })));

  this.buttons.push(new Button('load local', { x: 0, y: 0 }, ((b) => {
    loadLocal();
  })));

  this.buttons.push(new Button('ver: 0.1', { x: 0, y: 0 }, ((b) => {

  })));

  for (let i = 0; i < colors.length; i++) {
    const b = new Button('', { x: 0, y: 0 }, ((b) => {
      const rgb = hexToRgb(colors[i]);

      pen.set_color(rgb);

      for (let i = 0; i < objs.length; i++) {
        const obj = objs[i];
        if (typeof obj.set_color === 'function') {
          obj.set_color(rgb);
        }
      }
    }));
    b.color = colors[i];
    this.buttons.push(b);
  }

  for (let i = 0; i < this.buttons.length; i++) {
    const b = this.buttons[i];
    b.pos = { x: this.pos.x, y: this.pos.y + i * gridSize * 0.6 };
  }

  this.mouse_up = function (evt) {
    for (let i = 0; i < this.buttons.length; i++) {
      const btn = this.buttons[i];
      if (btn.mouse_up(evt)) {
        return true;
      }
    }

    return false;
  };

  this.render = function (ctx) {
    ctx.fillStyle = '#000000';
    for (let i = 0; i < this.buttons.length; i++) {
      const b = this.buttons[i];
      b.selected = false;
      if (b.text == tool) {
        b.selected = true;
      }
      b.render(ctx);
    }
  };
}

function Transition() {
  this.steps = 0;
  this.step = 0;
  this.transitioning = false;
  this.target_frame = 0;
  this.complete;

  this.run = function (steps, targetFrame, completion) {
    if (this.transitioning) {
      return;
    }

    tPercent = 0.0;
    tEase = 0.0;
    tInOut = 1.0;
    this.steps = steps;
    this.target_frame = targetFrame;
    this.transitioning = true;
    this.completion = completion;
  };

  this.update = function () {
    if (this.transitioning) {
      this.step += 1;
      tPercent = this.step / this.steps;
      tInOut = -math.cos(tPercent * 2 * math.PI - math.PI) / 2 + 0.5;
      parser.set('_t', tPercent);
      tEase = easeInOut(tPercent);
      parser.set('_tt', tEase);
      tEase = sigmoid(tPercent, 1.2, -0.4, 14) - sigmoid(tPercent, 0.2, -0.6, 15);
      if (this.step >= this.steps) {
        tPercent = 1.0;
        tInOut = 1.0;
        tEase = 1.0;
        this.completion(this.target_frame);
        this.step = 0;
        this.transitioning = false;
      }
    }
  };
}

function Pen() {
  this.drawings = {};
  this.path = [];
  this.path_nearby_idx = -1;
  this.color;

  this.onkeydown = function (evt) {
    if (tool == 'pen' && evt.key == 'Esc') {
      tool = 'select';
    } else if (evt.key == 'p') {
      if (tool == 'pen') {
        this.clear_drawing();
      }

      tool = 'pen';
    }

    if (tool == 'pen' && evt.key == 'Backspace') {
      // delete path nearby mouse
      if (this.path_nearby_idx != -1) {
        this.drawings[frame].splice(this.path_nearby_idx, 1);
      }
    }
  };

  this.mouse_down = function () {
    if (tool == 'pen') {
      this.path = [];
      return true;
    }

    return false;
  };

  this.mouse_move = function () {
    if (tool == 'pen') {
      this.path_nearby_idx = -1;

      if (mouseDown) {
        this.path.push([mouse.x, mouse.y]);
      }

      const drawing = this.drawings[frame];
      if (drawing) {
        for (let i = 0; i < drawing.length; i++) {
          const path = drawing[i].p;

          const x = path[0][0];
          const y = path[0][1];

          const xd = mouse.x - x;
          const yd = mouse.y - y;

          if (xd * xd + yd * yd < 200) {
            this.path_nearby_idx = i;
          }
        }
      }

      return true;
    }

    return false;
  };

  this.mouse_up = function () {
    if (tool == 'pen') {
      // add path to drawing
      if (this.path && this.path.length) {
        if (!this.drawings[frame]) {
          this.drawings[frame] = [];
        }

        this.drawings[frame].push({ p: this.path, c: this.color });
        this.path = [];
      }

      return true;
    }

    return false;
  };

  this.set_color = function (rgb) {
    if (tool == 'pen') {
      this.color = rgbToHex(rgb);
      return true;
    }

    return false;
  };

  this.clear_drawing = function () {
    if (this.drawings[frame]) {
      delete this.drawings[frame];
    }

    this.path = [];
  };

  this.render = function () {
    ctx.save();

    const drawPath = function (_path) {
      ctx.beginPath();
      const path = _path.p;
      const { c } = _path;

      ctx.strokeStyle = c;

      for (let j = 0; j < path.length; j++) {
        const x = path[j][0];
        const y = path[j][1];

        if (j == 0) {
          ctx.moveTo(x, y);
        } else {
          ctx.lineTo(x, y);
        }
      }

      ctx.stroke();
    };

    let frameToDraw = frame;

    if (transition.transitioning) {
      // fade in out
      ctx.globalAlpha = -math.cos(tPercent * 2 * math.PI - math.PI) / 2 + 0.5;
      if (tPercent > 0.5) {
        frameToDraw = nextFrame;
      }

      if (!this.drawings[nextFrame]) {
        // fade out
        ctx.globalAlpha = 1 - tPercent;
        frameToDraw = frame;
      }
    }

    if (this.drawings[frameToDraw]) {
      // draw the drawing
      for (let i = 0; i < this.drawings[frameToDraw].length; i++) {
        const path = this.drawings[frameToDraw][i];

        if (!presenting) {
          ctx.globalAlpha = 1;
          if (this.path_nearby_idx == i) {
            ctx.globalAlpha = 0.5;
          }
        }

        drawPath(path);
      }
    }

    if (this.path && this.path.length) {
      drawPath({ p: this.path, c: this.color });
    }

    /*
        if (!presenting) {
            // onion skin
            ctx.globalAlpha = .5;
            if (frame > 1) {
                if (this.drawings[frame-1]) {
                    // draw the drawing
                    for (let i = 0; i < this.drawings[frame-1].length; i ++) {
                        let path = this.drawings[frame-1][i];
                        draw_path(path);
                    }
                }
            }
        } */

    ctx.restore();
  };
}

function constrainFrame(f) {
  return Math.max(1, Math.min(numFrames, f));
}

function constrain(v) {
  return Math.min(1, Math.max(0, v));
}

function loopFrame(f) {
  if (f >= numFrames + 1) {
    return 1;
  } if (f < 1) {
    return numFrames;
  }

  return f;
}

function drawAxes(ctx) {
  if (!cam.R) {
    return;
  }

  ctx.save();

  const csysStyle = cam.style();
  props = cam.properties[frame];

  // do a fade in and out
  if (transition.transitioning) {
    const csysNextStyle = cam.properties[nextFrame].style;

    if (csysNextStyle != null && csysNextStyle != csysStyle) {
      // changing text
      const constrained = constrain(tEase);
      ctx.globalAlpha = Math.cos(constrained * 2 * Math.PI) / 2 + 0.5;
      if (constrained >= 0.5) {
        csysStyle = csysNextStyle;
        if (cam.properties[nextFrame]) {
          props = cam.properties[nextFrame];
        }
      }
    }
  }

  if (csysStyle == '3d' || csysStyle == 'flat') {
    // draw gridlines
    ctx.strokeStyle = '#DDDDDD';

    if (csysStyle == '3d') {
      let axis = cam.ticks[0];
      axis = math.matrix(axis);
      axis = cam.graph_to_screen_mat(axis);
      const N = axis.length;
      for (let j = 0; j < N; j += 2) {
        if (j == 20 || j == 62) {
          continue;
        }

        ctx.beginPath();
        ctx.moveTo(axis[j][0], axis[j][1]);
        ctx.lineTo(axis[j + 1][0], axis[j + 1][1]);
        ctx.stroke();
      }
    } else {
      const w = winWidth * 2;
      const h = winHeight * 2;

      const dx = gridSize * props.w;
      const dy = gridSize * props.h;

      const p = cam.graph_to_screen(0, 0, 0);

      for (let x = p[0] % dx; x < w; x += dx) {
        ctx.beginPath();
        ctx.moveTo(x, 0);
        ctx.lineTo(x, h);
        ctx.stroke();
      }

      for (let y = p[1] % dy; y < h; y += dy) {
        ctx.beginPath();
        ctx.moveTo(0, y);
        ctx.lineTo(w, y);
        ctx.stroke();
      }
    }

    ctx.textAlign = 'center';
    ctx.strokeStyle = '#000000';

    // center
    const c = cam.graph_to_screen(0, 0, 0);

    // axes
    let axes = math.matrix([[10, 0, 0],
      [0, 10, 0],
      [0, 0, 10],
      [-10, 0, 0],
      [0, -10, 0],
      [0, 0, -10]]);

    axes = cam.graph_to_screen_mat(axes);

    let labels;
    if (cam.axes_names) {
      labels = cam.axes_names;
    } else {
      labels = ['x', 'y', 'z'];
    }

    const colors = ['#FF0000', '#00FF00', '#0000FF'];

    N = axes.length;
    for (let i = 0; i < N; i++) {
      ctx.fillStyle = colors[i % 3];
      ctx.strokeStyle = colors[i % 3];

      x = axes[i][0];
      y = axes[i][1];

      ctx.beginPath();
      ctx.moveTo(c[0], c[1]);
      ctx.lineTo(x, y);
      ctx.stroke();
    }

    ctx.globalAlpha = 1;
    ctx.lineWidth = 0;

    for (let i = 0; i < 3; i++) {
      x = axes[i][0];
      y = axes[i][1];

      ctx.beginPath();
      ctx.fillStyle = '#FFFFFF';
      ctx.arc(x, y, 16, 0, 2 * Math.PI);
      ctx.fill();

      ctx.fillStyle = colors[i % 3];
      ctx.strokeStyle = colors[i % 3];
      ctx.fillText(labels[i], x, y);
    }
  }

  ctx.restore();
}

function transitionWithNext(next) {
  if (transition.transitioning) {
    return;
  }

  if (next > numFrames) {
    return;
  }

  if (tool == 'copy frame') {
    enterSelect();
    // copy properties
    for (let i = 0; i < objs.length; i++) {
      const obj = objs[i];
      if (typeof obj.copy_properties === 'function') {
        obj.copy_properties(frame, next);
      }
    }

    return;
  }

  newLine = null;
  nextFrame = next;
  changeFrames();
  let steps = tSteps;
  if (!presenting || meta || ctrl) {
    // make it instant when menu open
    steps = 0;
  }

  transition.run(steps, next, (targ) => {
    frame = targ;
    parser.set('frame', frame);

    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.parse_text === 'function') {
        obj.parse_text(obj.properties[frame].t);
      }

      if (typeof obj.eval === 'function') {
        obj.eval();
      }
    }
  });
}

function enterSelect() {
  tool = 'select';
  newLine = null;
}

function drawCursor() {
  if (presenting && tool == 'pen') {
    const pad = 20;

    ctx.save();

    ctx.translate(mouse.x, mouse.y);

    ctx.strokeStyle = pen.color;

    ctx.beginPath();
    ctx.moveTo(0, 0);
    ctx.lineTo(pad / 2, pad);
    ctx.moveTo(0, 0);
    ctx.lineTo(-pad / 2, pad);

    ctx.stroke();
    ctx.restore();
  } else if (presenting && mouseTime > 0) {
    // draw a cursor

    const mx = mouse.x;
    const my = mouse.y;

    ctx.save();
    ctx.translate(mx, my);
    ctx.strokeStyle = dark;
    ctx.beginPath();

    if (mouseDown) {
      mouseTime = mouseDuration;

      ctx.arc(0, 0, 10, 0, pi2, 0);
    } else {
      const pad = 20;

      if (tool == 'camera') {
        ctx.moveTo(-pad, 0);
        ctx.lineTo(pad, 0);
        ctx.moveTo(0, -pad);
        ctx.lineTo(0, pad);
      } else {
        ctx.moveTo(pad, 0);
        ctx.lineTo(0, 0);
        ctx.lineTo(0, pad);
        ctx.moveTo(0, 0);
        ctx.lineTo(pad, pad);
      }
    }

    ctx.stroke();
    ctx.restore();
  }
}

window.onload = function () {
  objs = [];

  c = document.createElement('canvas');
  winWidth = window.innerWidth;
  winHeight = window.innerHeight;
  c.width = winWidth * scaleFactor;
  c.height = winHeight * scaleFactor;
  c.style.width = winWidth;
  c.style.height = winHeight;

  ctx = c.getContext('2d');
  ctx.fillStyle = dark;
  ctx.strokeStyle = dark;
  ctx.lineWidth = 4;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'middle';
  ctx.lineJoin = 'round';

  // speech synth
  synth = window.speechSynthesis; // speech synthesis
  window.speechSynthesis.onvoiceschanged = function () {
    voices = window.speechSynthesis.getVoices();
  };

  const content = document.getElementById('content');
  content.appendChild(c);

  document.getElementById('save').onclick = function (evt) {
    save(objs);
    return false;
  };

  document.getElementById('file').onchange = function (evt) {
    enterSelect();
    load(evt);
  };

  document.getElementById('load_to_frame').onclick = function (evt) {
    const text = document.getElementById('selected_objects_text').value;
    const arr = JSON.parse(text);
    objs = objs.concat(textArrayToObjs(arr, false));
  };

  formulaText = document.getElementById('formula_text');
  document.getElementById('load_clear_formula_text').onclick = function (evt) {
    const t = formulaText.value;
    for (let i = 0; i < objs.length; i++) {
      const obj = objs[i];
      if (typeof obj.change_text === 'function' && obj.is_selected()) {
        obj.change_text(t);
      }
    }
  };
  document.getElementById('load_insert_formula_text').onclick = function (evt) {
    const t = formulaText.value;
    for (let i = 0; i < objs.length; i++) {
      const obj = objs[i];
      if (typeof obj.replace_selected_text === 'function' && obj.is_selected()) {
        obj.change_text(obj.replace_selected_text(t));
      }
    }
  };

  document.getElementById('gen_js').onclick = function (evt) {
    let js = '';

    for (let i = 0; i < selectedObjs.length; i++) {
      const obj = selectedObjs[i];
      if (obj.generate_javascript) {
        const s = obj.generate_javascript();
        js += `${s}\n`;
      }
    }

    document.getElementById('generic').value = js;
  };

  document.getElementById('gen_script').onclick = function (evt) {
    let script = document.getElementById('generic').value;
    script = script.split('\n');

    const sClean = [];
    for (let i = 0; i < script.length; i++) {
      const s = script[i];
      if (s.length != 0) {
        sClean.push(s);
      }
    }

    script = sClean;

    const t = new Text('', { x: 20, y: winHeight * 2 - 60 });
    t.properties[frame].w = 0.6;
    t.properties[frame].h = 0.6;
    objs.push(t);

    for (let i = 0; i < script.length; i++) {
      const s = script[i];
      const fr = i + 1;
      if (!t.properties[fr]) {
        t.properties[fr] = copy(t.properties[fr - 1]);
      }

      t.properties[fr].t = s;
    }

    numFrames = script.length;
    frames.create_buttons();

    saveState();
  };

  document.addEventListener('paste', (event) => {
    const paste = (event.clipboardData || window.clipboardData).getData('text');
    console.log(`pasting: ${paste}`);

    const N = objs.length;
    for (let i = 0; i < objs.length; i++) {
      const obj = objs[i];
      if (obj.type == 'Text') {
        if (obj.is_selected()) {
          obj.paste_text(paste);
        }
      }
    }

    event.preventDefault();
  });

  transition = new Transition();
  frame = 1;
  frames = new Frames({ x: c.width - gridSize * 2, y: gridSize / 4 });
  frames.on_click = function (idx) {
    transitionWithNext(idx);
  };

  menu = new Menu({ x: gridSize / 4, y: gridSize / 2 });
  cam = new Camera();
  pen = new Pen();

  $(window).focus(() => {
    meta = false;
    ctrl = false;
  });

  window.onkeydown = function (evt) {
    const { key } = evt;

    if (key == 'Escape' && presenting && tool != 'camera' && tool != 'pen') {
      presenting = false;
      document.body.style.cursor = '';
      document.body.style.overflow = 'scroll'; // Enable and show scrollbar
      return false;
    }

    if (key == 'Escape') {
      enterSelect();
    }

    if (key == 'Tab') {
      tab = true;
    }

    if (key == 'Meta') {
      meta = true;
    }

    if (key == 'Shift') {
      shift = true;
    }

    if (key == 'Control') {
      ctrl = true;
    }

    if (key == 'Backspace') {
      if (ctrl) {
        const N = objs.length;
        for (let i = 0; i < N; i++) {
          const obj = objs[i];
          if (obj.is_selected()) {
            obj.deleted = true;
          }
        }
      }
    }

    if (key == 'z' && (meta || ctrl)) {
      undo();
      return;
    }

    if ((meta || ctrl) && key == 'Enter') {
      present();
      return true;
    }

    if (document.getElementById('formula_text') == document.activeElement) {
      return true;
    }

    let captured = false;
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];

      if (typeof obj.onkeydown === 'function') {
        if (obj.onkeydown(evt)) {
          captured = true;
          if (key == 'ArrowUp' || key == 'ArrowDown') {
            // stops text selection from propagating as you iterate the array
            break;
          }
        }
      }
    }

    if (captured) {
      return false;
    }

    if (frames.onkeydown(evt)) {
      return false;
    }

    cam.onkeydown(evt);
    pen.onkeydown(evt);

    if (key == ' ') {
      return false;
    }

    if (tool == 'select' && evt.srcElement == document.body) {
      tools = {
        t: 'text', s: 'shape', c: 'camera', v: 'vector',
      };
      if (key in tools) {
        tool = tools[key];
      }
    }
  };

  window.onkeyup = function (evt) {
    const { key } = evt;

    if (key == 'Tab') {
      tab = false;
    }

    if (key == 'Meta') {
      meta = false;
    }

    if (key == 'Shift') {
      shift = false;
    }

    if (key == 'Control') {
      ctrl = false;
    }

    saveState();
  };

  window.onmousedown = function (evt) {
    if (evt.srcElement != c) {
      return;
    }

    mouseDown = true;
    mouseStart = getMousePos(c, evt);

    try {
      math.compile('click()').eval(parser.scope);
    } catch (e) {

    }

    if (cam.mouse_down(evt)) {
      return;
    }

    if (pen.mouse_down(evt)) {
      return;
    }

    if (presenting) {
      return false;
    }

    let captured = false;
    for (let i = objs.length - 1; i >= 0; i--) {
      const obj = objs[i];
      if (typeof obj.mouse_down === 'function') {
        if (obj.mouse_down(evt)) {
          captured = true;
          break;
        }
      }
    }

    if (captured) {
      return false;
    }

    if (frames.mouse_down()) {
      return;
    }

    // didn't touch an obj, if tool is move start a rect
    let objSelected = false;
    const N = objs.length;
    for (let i = 0; i < N; i++) {
      if (objs[i].is_selected()) {
        objSelected = true;
      }
    }

    if (tool == 'select' && objSelected == false) {
      selecting = true;
    }
  };

  window.onmousemove = function (evt) {
    // update mouse
    mouse = getMousePos(c, evt);
    mouseGrid = constrainToGrid(mouse);
    mouseGraph = cam.screen_to_graph(mouse);

    parser.set('_y', mouseGraph.x);
    parser.set('_z', mouseGraph.y);

    if (pen.mouse_move(evt)) {
      return;
    }

    if (mouseDown) {
      let captured = false;
      const N = objs.length;
      for (let i = N - 1; i >= 0; i--) {
        const obj = objs[i];
        if (!captured && typeof obj.mouse_drag === 'function') {
          captured = obj.mouse_drag(evt);
        }
      }

      if (!captured) {
        cam.mouse_drag(evt);
      }
    } else {
      const N = objs.length;
      for (let i = 0; i < N; i++) {
        const obj = objs[i];
        if (typeof obj.mouse_move === 'function') {
          obj.mouse_move(evt);
        }
      }
    }

    if (presenting) {
      mouseTime = mouseDuration;
    }

    mouseLast = getMousePos(c, evt);
    mouseGridLast = constrainToGrid(mouse);
  };

  window.onmouseup = function (evt) {
    if (evt.srcElement != c) {
      return;
    }

    mouseDown = false;

    if (presenting) {
      // maybe tap some text
      let captured = false;
      const N = objs.length;
      for (let i = 0; i < N; i++) {
        const obj = objs[i];
        if (!captured && typeof obj.mouse_up === 'function') {
          captured = obj.mouse_up(evt);
        }
      }

      return false;
    }

    if (frames.mouse_up(evt)) {
      return;
    }

    if (menu.mouse_up(evt)) {
      newLine = null;
      selecting = false;

      saveState();
      return;
    }

    if (pen.mouse_up(evt)) {
      saveState();
      return;
    }

    if (tool == 'select') {
      let captured = false;
      const N = objs.length;
      for (let i = N - 1; i >= 0; i--) {
        const obj = objs[i];
        if (!captured && typeof obj.mouse_up === 'function') {
          captured = obj.mouse_up(evt);
        }
      }
    } else if (tool == 'text') {
      // add a num obj at mouse pos
      const n = new Text('', mouseGrid);

      const N = objs.length;
      for (let i = 0; i < N; i++) {
        const obj = objs[i];
        if (typeof obj.is_selected === 'function') {
          obj.selected = false;
        }
      }

      n.select();
      objs.push(n);
    } else if (tool == 'shape' || tool == 'vector') {
      // add a num obj at mouse pos
      if (newLine) {
        // add a point
        newLine.add_point({ x: mouseGrid.x, y: mouseGrid.y });
      } else {
        const l = new Shape([0, 0, 0, 1], [{ x: mouseGrid.x, y: mouseGrid.y }]);

        if (tool == 'vector') {
          l.properties[frame].v = true;
        } else if (tool == 'circle') {
          l.properties[frame].circle = true;
        }

        objs.push(l);
        newLine = l;
      }

      return;
    } else if (tool == 'circle') {
      const newCircle = new Circle([0, 0, 0, 1], mouseGrid);
      objs.push(newCircle);
    } else if (tool == 'network') {
      const n = new Network(mouseGrid);
      objs.push(n);
    }

    if (selecting) {
      selecting = false;

      const { x } = mouseStart;
      const { y } = mouseStart;
      const x2 = mouse.x;
      const y2 = mouse.y;

      xx = Math.min(x, x2);
      yy = Math.min(y, y2);
      xx2 = Math.max(x, x2);
      yy2 = Math.max(y, y2);

      selectedObjs = [];

      for (let i = 0; i < objs.length; i++) {
        const obj = objs[i];
        if (typeof obj.in_rect === 'function') {
          obj.in_rect(xx, yy, xx2, yy2);
          if (obj.is_selected()) {
            selectedObjs.push(obj);
          }
        }
      }

      const scopy = copy(selectedObjs);
      for (let i = 0; i < scopy.length; i++) {
        const obj = scopy[i];
        const props = copy(obj.properties[frame]);
        obj.properties = { 1: props };
      }

      if (scopy.length > 0) {
        // store as text rep
        const string = JSON.stringify(scopy);
        document.getElementById('selected_objects_text').value = string;
      }

      saveState();
      return false;
    }

    saveState();
  };

  window.ontouchstart = window.onmousedown;
  window.ontouchmove = window.onmousemove;
  window.ontouchend = window.onmouseup;

  saveState();

  let fps;
  millis = Date.now();
  let targMillis = millis + 1; // set below

  function animate() {
    millis = Date.now();
    if (millis < targMillis) {
      setTimeout(animate, targMillis - millis);
      return;
    }

    targMillis = millis + 1000 / fps;

    if (presenting) {
      fps = 60;
    } else {
      fps = 30; // save power when editing
    }

    parser.set('_frame', t);
    parser.set('_millis', millis);
    const mp = cam.screen_to_graph({ x: mouse.x, y: mouse.y });
    parser.set('_mx', mp.x);
    parser.set('_my', mp.y);

    if (meter) {
      parser.set('_vol', meter.volume);
    }

    if (presenting) {
      mouseTime -= 1;
    }

    if (!parser.get('_trace')) {
      ctx.clearRect(0, 0, c.width, c.height);
    }

    cam.update_props();

    drawAxes(ctx);

    ctx.font = fontAnim;

    const N = objs.length;
    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      if (typeof obj.eval === 'function') {
        obj.eval();
      }
    }

    for (let i = 0; i < N; i++) {
      const obj = objs[i];
      obj.render(ctx);
    }

    for (let i = objs.length - 1; i >= 0; i--) {
      const obj = objs[i];
      if (obj.deleted) {
        objs.splice(i, 1);
      }
    }

    if (selecting) {
      // draw a rect
      ctx.strokeStyle = dark;
      ctx.strokeRect(mouseStart.x, mouseStart.y, mouse.x - mouseStart.x, mouse.y - mouseStart.y);
    }

    ctx.font = fontMenu;

    if (!presenting) {
      frames.render(ctx);
      menu.render(ctx);

      if (errorTimer > 0) {
        ctx.save();
        ctx.fillStyle = 'red';
        ctx.fillText(errorText, 250, 30);
        ctx.restore();
        errorTimer -= 1;
      }
    }

    pen.render();

    drawCursor();

    if (viewFrame) {
      ctx.save();
      ctx.strokeStyle = 'black';
      ctx.beginPath();
      const w = 1928; // +8 pixels for padding
      const h = 1088;
      ctx.rect(winWidth - w / 2, winHeight - h / 2, w, h);
      ctx.stroke();

      if (!presenting) {
        ctx.globalAlpha = 0.1;

        ctx.beginPath();
        ctx.moveTo(winWidth - w / 2, winHeight);
        ctx.lineTo(winWidth + w / 2, winHeight);
        ctx.stroke();

        ctx.beginPath();
        ctx.moveTo(winWidth, winHeight - h / 2);
        ctx.lineTo(winWidth, winHeight + h / 2);
        ctx.stroke();

        ctx.globalAlpha = 1;
      }

      ctx.restore();
    }

    transition.update();

    t += 1;

    requestAnimationFrame(animate);
  }

  requestAnimationFrame(animate);
};
