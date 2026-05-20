'use strict';

const COLS = 47;
const ROWS = 25;
const TREASURE_TOTAL = 4;
const QUESTION_STEP_INTERVAL = 20;
const PLAYER_RADIUS = 0.27;
const SPEED_CELLS_PER_SEC = 2.35; // movimiento pausado, fluido y controlado
const MAX_SECURITY_LOCKS = 5;
const MAX_SCORE = 5.0;
const OBSTACLE_TOTAL = 20;
const PORTAL_TOTAL = 10;
const TRAP_TOTAL = 30;
const EXIT_TRANSPORTER_TOTAL = 22;
const EXIT_PORTAL_EXCLUSION_RADIUS = 8;
const EXIT_ACCESS_CORRIDOR_LENGTH = 5;
const EXIT_TRANSPORTER_RING_RADIUS = 5;
const FINAL_CHALLENGE_TOTAL = 3;
const FINAL_CHALLENGE_ICON = '🐲';

const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');

const screens = {
  menu: document.getElementById('menu'),
  game: document.getElementById('game')
};
const hud = {
  score: document.getElementById('scoreHud'),
  treasure: document.getElementById('treasureHud'),
  steps: document.getElementById('stepsHud'),
  difficulty: document.getElementById('difficultyHud'),
  mission: document.getElementById('missionText'),
  log: document.getElementById('eventLog')
};

const questionModal = document.getElementById('questionModal');
const questionTitle = document.getElementById('questionTitle');
const questionBadge = document.getElementById('questionBadge');
const questionText = document.getElementById('questionText');
const hintText = document.getElementById('hintText');
const answerForm = document.getElementById('answerForm');
const feedbackBox = document.getElementById('feedbackBox');
const hintBtn = document.getElementById('hintBtn');
const submitAnswerBtn = document.getElementById('submitAnswerBtn');
const continueBtn = document.getElementById('continueBtn');
const howModal = document.getElementById('howModal');
const endModal = document.getElementById('endModal');
const endTitle = document.getElementById('endTitle');
const endSummary = document.getElementById('endSummary');
const deviceClockValue = document.getElementById('deviceClockValue');
const clockHud = document.getElementById('clockHud');

let selectedAnimal = '🐉';
let tile = 22, offsetX = 0, offsetY = 0;
let lastTime = performance.now();
let activeQuestion = null;
let currentAnswerResult = null;
let pendingAfterQuestion = null;
let gameRunning = false;
let modalOpen = false;
let securityLockActive = false;
let lastSecurityEventAt = 0;

const keys = new Set();
const keyToDir = {
  ArrowUp: {x:0,y:-1}, ArrowDown: {x:0,y:1}, ArrowLeft:{x:-1,y:0}, ArrowRight:{x:1,y:0},
  w:{x:0,y:-1}, W:{x:0,y:-1}, s:{x:0,y:1}, S:{x:0,y:1}, a:{x:-1,y:0}, A:{x:-1,y:0}, d:{x:1,y:0}, D:{x:1,y:0}
};
let currentDir = {x:0,y:0};

const state = {
  grid: [],
  player: {x:1.5,y:1.5},
  start: {x:1,y:1},
  exit: {x:Math.floor(COLS/2), y:Math.floor(ROWS/2)},
  score: 1.0,
  steps: 0,
  lastQuestionStep: 0,
  treasuresFound: 0,
  treasures: [],
  portals: [],
  exitTransporters: [],
  exitSafeKeys: new Set(),
  finalChallengeCells: new Set(),
  exitAccessCell: null,
  obstacles: new Set(),
  bonusCells: new Set(),
  trapCells: new Set(),
  answered: [],
  log: [],
  visitedCell: '',
  startedAt: null,
  finishedAt: null,
  security: { locks:0, fullscreenExits:0, focusLosses:0, hiddenTabs:0, escapeKey:0, rightClicks:0, printScreen:0, blockedShortcuts:0, wrongTeacherCodes:0 },
  cancelled: false
};

const TREASURE_ICONS = ['🏮','🧧','🏯','🪭'];
const TREASURE_NAMES = ['Linterna de la Razón','Sobre Rojo de la Raíz','Pagoda de la Comparación','Abanico del Integral'];
const OBSTACLE_ICONS = ['🧱','🏯','🎎','⛩️','🪭','🎋'];
const PORTAL_ICON = '🌀';
const EXIT_TRANSPORTER_ICON = '🎋';
const BONUS_ICON = '🧧';
const TRAP_ICON = '🔥';

const QUESTIONS_PER_TYPE = 10000;
const QUESTION_TYPE_TOTALS = {
  tf: QUESTIONS_PER_TYPE,
  statements: QUESTIONS_PER_TYPE,
  integer: QUESTIONS_PER_TYPE,
  choice: QUESTIONS_PER_TYPE
};
const QUESTION_BANK_TOTAL = Object.values(QUESTION_TYPE_TOTALS).reduce((a,b)=>a+b,0);
const STATEMENT_OPTIONS = ['Solo I','Solo II','Solo III','I y II','I y III','II y III','I, II y III','Ninguna'];
const TOPICS = ['Sucesiones','Series numéricas','Criterio de la razón','Criterio de la raíz','Comparación al límite','Criterio integral','Serie geométrica','Serie p-armónica'];
const questionBank = buildQuestionBank();


// Utilidades esenciales del motor del juego.
// En la versión anterior estas funciones quedaron ausentes y por eso el botón
// “Entrar a la muralla” podía mostrar un error antes de iniciar el laberinto.
function randInt(n){
  const m = Math.max(0, Math.floor(Number(n) || 0));
  return m <= 0 ? 0 : Math.floor(Math.random() * m);
}
function clamp(value, min, max){
  const v = Number(value);
  if(Number.isNaN(v)) return min;
  return Math.max(min, Math.min(max, v));
}
function keyOf(x,y){ return `${Math.floor(x)},${Math.floor(y)}`; }
function cellOf(pos){
  return {
    x: clamp(Math.floor(pos.x), 0, COLS - 1),
    y: clamp(Math.floor(pos.y), 0, ROWS - 1)
  };
}
function showScreen(name){
  Object.entries(screens).forEach(([key,screen]) => {
    if(!screen) return;
    if(key === name) screen.classList.add('active');
    else screen.classList.remove('active');
  });
}

function buildQuestionBank(){
  // Banco virtual/lazy: no se construyen 40.000 objetos al cargar la página.
  // Cada pregunta se genera al momento de necesitarse, usando índices de 0 a 9.999 por tipo.
  // Esto conserva 10.000 posibilidades por tipo sin bloquear el botón de inicio.
  return {
    mode: 'lazy',
    perType: QUESTIONS_PER_TYPE,
    types: ['tf','statements','integer','choice'],
    total: QUESTION_BANK_TOTAL
  };
}
function makeGeneratedQuestion(type,i){
  if(type === 'tf') return makeTFQuestion(i);
  if(type === 'statements') return makeStatementsQuestion(i);
  if(type === 'integer') return makeIntegerQuestion(i);
  return makeChoiceQuestion(i);
}
function difficultyFor(i,shift=0){
  const levels = ['basico','medio','avanzado','experto','bono'];
  return levels[(i + shift) % levels.length];
}
function valueFrom(i, mult, mod, add=0){ return ((i * mult + add) % mod); }
function signedCenter(i){ return valueFrom(i,7,13) - 6; }
function positiveA(i){ return 2 + valueFrom(i,5,9); }
function positiveB(i){ return 1 + valueFrom(i,11,7); }
function binomial(n,k){
  if(k<0 || k>n) return 0;
  k = Math.min(k,n-k);
  let r=1;
  for(let j=1;j<=k;j++) r = Math.round(r * (n-k+j) / j);
  return r;
}
function statementAnswer(flags){
  const names = ['I','II','III'];
  const chosen = flags.map((v,i)=>v ? names[i] : null).filter(Boolean);
  if(chosen.length===0) return 'Ninguna';
  if(chosen.length===3) return 'I, II y III';
  if(chosen.length===1) return `Solo ${chosen[0]}`;
  return chosen.join(' y ');
}
function shuffledOptions(options){ return shuffle(options).map(String); }
function intervalText(left,right,leftClosed,rightClosed){
  return `\\(${leftClosed?'[':'('}${left},${right}${rightClosed?']':')'}\\)`;
}
function questionId(prefix,i,extra=''){
  return `${prefix}-${String(i+1).padStart(5,'0')}-${extra}`;
}

function gcd(a,b){ a=Math.abs(Math.trunc(a)); b=Math.abs(Math.trunc(b)); while(b){ const t=a%b; a=b; b=t; } return a || 1; }
function fracTex(num,den){ const g=gcd(num,den); num=Math.trunc(num/g); den=Math.trunc(den/g); return den===1 ? String(num) : `\\frac{${num}}{${den}}`; }
function convWord(v){ return v ? 'converge' : 'diverge'; }
function makeTFQuestion(i){
  const t=i%8, diff=difficultyFor(i,0), a=2+valueFrom(i,5,8), b=3+valueFrom(i,7,8), p=1+valueFrom(i,11,4), truth=valueFrom(i,37,2)===0;
  const topic=TOPICS[valueFrom(i,13,TOPICS.length)]; let prompt='',hint='',solution='',answer=truth?'Verdadero':'Falso',title='Verdadero o falso';
  if(t===0){ const claimed=truth?a:a+1; prompt=`Determina si la afirmación es verdadera o falsa: para \\(a_n=\\frac{${a}n+1}{n+${b}}\\), se tiene \\(\\lim_{n\\to\\infty}a_n=${claimed}\\).`; hint=`Compara los coeficientes de la potencia dominante de \\(n\\).`; solution=`Dividiendo por \\(n\\), \\(a_n=\\frac{${a}+1/n}{1+${b}/n}\\to ${a}\\). La afirmación ${truth?'coincide':'no coincide'} con el límite.`; }
  else if(t===1){ const actual=p>1, stated=truth?actual:!actual; prompt=`Decide si es verdadera o falsa: la serie \\(\\sum_{n=1}^{\\infty}1/n^{${p}}\\) ${convWord(stated)}.`; hint=`Clasifica la serie como \\(p\\)-armónica y recuerda el exponente crítico.`; solution=`Una serie \\(p\\)-armónica converge si \\(p>1\\). Aquí \\(p=${p}\\), por tanto ${convWord(actual)}.`; }
  else if(t===2){ const actual=a<b, stated=truth?actual:!actual; prompt=`Verdadero o falso: la serie geométrica \\(\\sum_{n=0}^{\\infty}(${fracTex(a,b)})^n\\) ${convWord(stated)}.`; hint=`Identifica la razón común \\(r\\) y revisa si \\(|r|<1\\).`; solution=`La razón es \\(${fracTex(a,b)}\\). Una geométrica converge si \\(|r|<1\\); aquí ${convWord(actual)}.`; }
  else if(t===3){ const actual=a<b, stated=truth?actual:!actual; prompt=`Sea \\(\\sum_{n=1}^{\\infty}\\frac{${a}^n}{${b}^n+n}\\). La afirmación dice que por razón la serie ${convWord(stated)}.`; hint=`Mira el cociente \\(a_{n+1}/a_n\\); dominan las partes exponenciales.`; solution=`El cociente se comporta como \\(${fracTex(a,b)}\\). Converge si ese límite es menor que \\(1\\); aquí ${convWord(actual)}.`; }
  else if(t===4){ const actual=a<b, stated=truth?actual:!actual; prompt=`Verdadero o falso: \\(\\sum_{n=1}^{\\infty}(${fracTex(a,b)})^n(1+1/n)^n\\) ${convWord(stated)} por el criterio de la raíz.`; hint=`Extrae raíz \\(n\\)-ésima y observa qué factor tiende a \\(1\\).`; solution=`La raíz \\(n\\)-ésima tiende a \\(${fracTex(a,b)}\\). Entonces la serie ${convWord(actual)}.`; }
  else if(t===5){ const actual=p>1, stated=truth?actual:!actual; prompt=`Verdadero o falso: por comparación al límite con \\(\\sum 1/n^{${p}}\\), la serie \\(\\sum_{n=1}^{\\infty}\\frac{${a}n+1}{n^{${p+1}}+1}\\) ${convWord(stated)}.`; hint=`Compara potencias dominantes y mira si queda una constante positiva por \\(1/n^p\\).`; solution=`El término es asintótico a \\(${a}/n^{${p}}\\), así que se comporta como \\(\\sum 1/n^{${p}}\\); por tanto ${convWord(actual)}.`; }
  else if(t===6){ const actual=p>1, stated=truth?actual:!actual; prompt=`Decide si es verdadera o falsa: \\(\\sum_{n=2}^{\\infty}1/[n(\\ln n)^{${p}}]\\) ${convWord(stated)} por el criterio integral.`; hint=`Relaciona con la integral impropia y usa el cambio \\(u=\\ln x\\).`; solution=`La integral asociada converge exactamente si \\(p>1\\). Aquí \\(p=${p}\\), por tanto ${convWord(actual)}.`; }
  else { const stated=truth?false:true; }
  if(t===7){ const L=1+valueFrom(i,3,5), stated=truth?false:true; prompt=`Verdadero o falso: \\(\\sum_{n=1}^{\\infty}\\frac{${L}n+1}{n+${L}}\\) ${convWord(stated)}.`; hint=`Antes de usar criterios avanzados, verifica si el término general tiende a cero.`; solution=`El término general tiende a \\(${L}\\neq0\\). Por la prueba del término general, la serie diverge.`; }
  return {id:questionId('tf',i,`${t}-${diff}`), difficulty:diff, type:'tf', topic, title, prompt, options:['Verdadero','Falso'], answer, hint, solution};
}
function makeStatementsQuestion(i){
  const t=i%6, diff=difficultyFor(i,1), a=2+valueFrom(i,5,8), b=3+valueFrom(i,7,8), p=1+valueFrom(i,11,4), k=2+valueFrom(i,13,6);
  let flags=[true,false,true], prompt='', hint='', solution='', topic=TOPICS[valueFrom(i,17,TOPICS.length)], title='Afirmaciones I, II y III';
  if(t===0){ const conv=p>1; flags=[true,conv,!conv]; prompt=`Para \\(\\sum 1/n^{${p}}\\): \\[\\text{I. Es }p\\text{-armónica.}\\]\\[\\text{II. Converge.}\\]\\[\\text{III. Diverge.}\\]`; hint=`Ubica el exponente frente al umbral \\(p=1\\).`; solution=`I es verdadera. Como \\(p=${p}\\), la serie ${convWord(conv)}.`; }
  else if(t===1){ const conv=a<b; flags=[true,conv,!conv]; prompt=`Para \\(\\sum (${fracTex(a,b)})^n\\): \\[\\text{I. Es geométrica.}\\]\\[\\text{II. Converge.}\\]\\[\\text{III. Diverge.}\\]`; hint=`Revisa la razón común y su valor absoluto.`; solution=`La razón es \\(${fracTex(a,b)}\\), por eso la serie ${convWord(conv)}.`; }
  else if(t===2){ const conv=a<b; flags=[true,conv,!conv]; prompt=`Para \\(\\sum \\frac{${a}^n}{${b}^n+n^2}\\): \\[\\text{I. Razón es un criterio natural.}\\]\\[\\text{II. Converge.}\\]\\[\\text{III. Diverge.}\\]`; hint=`Observa que predominan potencias exponenciales.`; solution=`El límite del cociente se comporta como \\(${fracTex(a,b)}\\). Entonces ${convWord(conv)}.`; }
  else if(t===3){ const conv=p>1; flags=[true,true,conv]; prompt=`Para \\(\\sum \\frac{${k}n+1}{n^{${p+1}}+1}\\): \\[\\text{I. }a_n\\sim ${k}/n^{${p}}.\\]\\[\\text{II. Sirve comparación al límite.}\\]\\[\\text{III. Converge.}\\]`; hint=`Compara las potencias dominantes y luego con una \\(p\\)-serie.`; solution=`I y II son verdaderas. III depende de \\(p>1\\); aquí la serie ${convWord(conv)}.`; }
  else if(t===4){ const conv=p>1; flags=[true,conv,!conv]; prompt=`Para \\(\\sum_{n=2}^\\infty 1/[n(\\ln n)^{${p}}]\\): \\[\\text{I. Se puede usar criterio integral.}\\]\\[\\text{II. Converge.}\\]\\[\\text{III. Diverge.}\\]`; hint=`Piensa en la integral con sustitución logarítmica.`; solution=`La integral correspondiente converge si \\(p>1\\). Aquí ${convWord(conv)}.`; }
  else { flags=[true,false,true]; prompt=`Para \\(\\sum \\frac{${k}n+1}{n+${a}}\\): \\[\\text{I. El término general no tiende a cero.}\\]\\[\\text{II. La serie converge.}\\]\\[\\text{III. Diverge por la prueba del término general.}\\]`; hint=`Revisa el límite del término general antes de aplicar otros criterios.`; solution=`El término tiende a \\(${k}\\neq0\\). Por eso I y III son verdaderas.`; }
  const answer=statementAnswer(flags); return {id:questionId('st',i,`${t}-${diff}`), difficulty:diff, type:'statements', topic, title, prompt, options:shuffledOptions(STATEMENT_OPTIONS), answer, hint, solution};
}
function makeIntegerQuestion(i){
  const t=i%8, diff=difficultyFor(i,2), a=2+valueFrom(i,5,8), b=3+valueFrom(i,7,8), p=1+valueFrom(i,11,4), k=2+valueFrom(i,13,6);
  let prompt='',hint='',solution='',answer=0,topic=TOPICS[valueFrom(i,19,TOPICS.length)],title='Respuesta entera';
  if(t===0){ prompt=`Para \\(a_n=\\frac{${a}n+${k}}{n+${b}}\\), escribe \\(\\lim a_n\\).`; hint=`Compara coeficientes principales.`; answer=a; solution=`El límite es \\(${a}/1=${a}\\).`; }
  else if(t===1){ prompt=`Escribe el menor entero \\(p\\) para que \\(\\sum 1/n^p\\) converja.`; hint=`Recuerda el umbral de la serie \\(p\\)-armónica.`; answer=2; solution=`Converge si \\(p>1\\), así que el menor entero es \\(2\\).`; }
  else if(t===2){ const g=gcd(a,b); prompt=`En \\(\\sum (${fracTex(a,b)})^n\\), escribe el denominador de la razón simplificada.`; hint=`Simplifica la fracción de la razón común.`; answer=b/g; solution=`La razón simplificada es \\(${fracTex(a,b)}\\), denominador \\(${b/g}\\).`; }
  else if(t===3){ const g=gcd(a,b); prompt=`Para el criterio de la raíz aplicado a \\(\\sum (${fracTex(a,b)})^n(1+1/n)^n\\), escribe el numerador del límite simplificado.`; hint=`La raíz \\(n\\)-ésima deja la razón y un factor que tiende a \\(1\\).`; answer=a/g; solution=`El límite es \\(${fracTex(a,b)}\\); su numerador simplificado es \\(${a/g}\\).`; }
  else if(t===4){ prompt=`Escribe el menor entero \\(p\\) para que \\(\\sum_{n=2}^\\infty 1/[n(\\ln n)^p]\\) converja.`; hint=`Usa el criterio integral.`; answer=2; solution=`Converge exactamente si \\(p>1\\).`; }
  else if(t===5){ prompt=`Calcula \\(\\lim_{n\\to\\infty}\\frac{\\frac{${k}n+1}{n^{${p+1}}+1}}{1/n^{${p}}}\\).`; hint=`Multiplica por \\(n^p\\) y compara términos dominantes.`; answer=k; solution=`El límite es \\(${k}\\).`; }
  else if(t===6){ prompt=`Para \\(\\sum (${fracTex(1,k)})^n\\), escribe el denominador de la razón común.`; hint=`La razón común es el factor entre términos consecutivos.`; answer=k; solution=`La razón es \\(1/${k}\\).`; }
  else { prompt=`La serie telescópica \\(\\sum_{n=1}^{\\infty}1/[n(n+1)]\\) converge. Escribe su suma.`; hint=`Usa \\(1/[n(n+1)]=1/n-1/(n+1)\\).`; answer=1; solution=`Las sumas parciales son \\(1-1/(N+1)\\), que tienden a \\(1\\).`; }
  return {id:questionId('int',i,`${t}-${diff}`), difficulty:diff, type:'integer', topic, title, prompt, answer:String(answer), hint, solution};
}
function makeChoiceQuestion(i){
  const t=i%7, diff=difficultyFor(i,3), a=2+valueFrom(i,5,8), b=3+valueFrom(i,7,8), p=1+valueFrom(i,11,4), k=2+valueFrom(i,13,6);
  const topic=TOPICS[valueFrom(i,23,TOPICS.length)]; let prompt='',hint='',solution='',answer='',options=[],title='Selección múltiple';
  if(t===0){ answer=p>1?'Converge':'Diverge'; prompt=`Selecciona la conclusión para \\(\\sum 1/n^{${p}}\\).`; hint=`Es una serie \\(p\\)-armónica.`; solution=`Como \\(p=${p}\\), la serie ${answer.toLowerCase()}.`; options=shuffledOptions([answer, answer==='Converge'?'Diverge':'Converge','No concluye','Converge por telescopaje']); }
  else if(t===1){ answer=a<b?'Converge por ser geométrica con |r|<1':'Diverge porque |r| no es menor que 1'; prompt=`Elige la justificación para \\(\\sum (${fracTex(a,b)})^n\\).`; hint=`Identifica la razón común.`; solution=`La razón es \\(${fracTex(a,b)}\\).`; options=shuffledOptions([answer,'Criterio integral','Comparación al límite con logaritmos','No hay razón común']); }
  else if(t===2){ answer='Criterio de la razón'; prompt=`¿Qué criterio conviene para \\(\\sum ${a}^n/n!\\)?`; hint=`Factoriales se simplifican con cocientes consecutivos.`; solution=`El cociente lleva a \\(${a}/(n+1)\\to0\\).`; options=shuffledOptions([answer,'Criterio integral','Telescopaje','Comparación directa con 1/n']); }
  else if(t===3){ answer='Criterio de la raíz'; prompt=`¿Qué criterio conviene para \\(\\sum (${fracTex(a,b)})^n(1+1/n)^n\\)?`; hint=`Hay potencias \\(n\\) sobre varios factores.`; solution=`La raíz \\(n\\)-ésima da un límite directo.`; options=shuffledOptions([answer,'Criterio integral','Leibniz','Telescopaje']); }
  else if(t===4){ answer='Comparación al límite'; prompt=`Para \\(\\sum (${k}n+1)/(n^{${p+1}}+1)\\), ¿qué criterio se ajusta al comparar con \\(\\sum1/n^{${p}}\\)?`; hint=`Busca un cociente que tienda a constante positiva.`; solution=`El cociente con \\(1/n^{${p}}\\) tiende a \\(${k}\\).`; options=shuffledOptions([answer,'Criterio de la raíz','Serie geométrica exacta','Criterio integral obligatorio']); }
  else if(t===5){ answer='Criterio integral'; prompt=`¿Qué criterio es natural para \\(\\sum_{n=2}^\\infty1/[n(\\ln n)^{${p}}]\\)?`; hint=`Observa la forma logarítmica asociada a una integral impropia.`; solution=`Se estudia con \\(\\int dx/[x(\\ln x)^p]\\).`; options=shuffledOptions([answer,'Criterio de la razón','Criterio de la raíz','Prueba de sucesión monótona']); }
  else { answer='Diverge por la prueba del término general'; prompt=`Selecciona la conclusión para \\(\\sum (${k}n+1)/(n+${a})\\).`; hint=`Primero mira si el término general tiende a cero.`; solution=`El término general tiende a \\(${k}\\neq0\\).`; options=shuffledOptions([answer,'Converge por comparación','Converge por integral','No se puede decidir']); }
  return {id:questionId('ch',i,`${t}-${diff}`), difficulty:diff, type:'choice', topic, title, prompt, options, answer, hint, solution};
}

function shuffle(arr){
  const a = arr.slice();
  for(let i=a.length-1;i>0;i--){const j=randInt(i+1);[a[i],a[j]]=[a[j],a[i]];}
  return a;
}
function ellipseMetrics(margin=0){
  const cx=(COLS-1)/2, cy=(ROWS-1)/2;
  const rx=(COLS-3)/2 - margin, ry=(ROWS-3)/2 - margin;
  return {cx,cy,rx,ry};
}
function ellipseCoords(x,y,margin=0){
  const {cx,cy,rx,ry}=ellipseMetrics(margin);
  const nx=(x-cx)/rx, ny=(y-cy)/ry;
  return {nx,ny,r:Math.hypot(nx,ny),a:Math.atan2(ny,nx)};
}
function insideEllipse(x,y,margin=0){
  return ellipseCoords(x,y,margin).r <= 1;
}
function angleDistance(a,b){
  let d=Math.abs(a-b)%(Math.PI*2);
  return d>Math.PI ? Math.PI*2-d : d;
}
function isPathChar(ch){ return ch === '.' || ch === 'S' || ch === 'E'; }
function isWallCell(x,y){
  if(x<0||y<0||x>=COLS||y>=ROWS) return true;
  return state.grid[y]?.[x] === '#';
}
function isFreeAt(x,y){
  const pts = [[x,y],[x-PLAYER_RADIUS,y],[x+PLAYER_RADIUS,y],[x,y-PLAYER_RADIUS],[x,y+PLAYER_RADIUS],[x-PLAYER_RADIUS*.72,y-PLAYER_RADIUS*.72],[x+PLAYER_RADIUS*.72,y+PLAYER_RADIUS*.72],[x-PLAYER_RADIUS*.72,y+PLAYER_RADIUS*.72],[x+PLAYER_RADIUS*.72,y-PLAYER_RADIUS*.72]];
  return pts.every(([px,py]) => !isWallCell(Math.floor(px), Math.floor(py)));
}
function pathCells(){
  const cells=[];
  for(let y=1;y<ROWS-1;y++) for(let x=1;x<COLS-1;x++){
    if(isPathChar(state.grid[y][x])) cells.push({x,y});
  }
  return cells;
}
function dist(a,b){ return Math.hypot(a.x-b.x,a.y-b.y); }
function distanceToExitCell(c){ return dist(c,state.exit); }
function difficultyAtPlayer(){
  const d = dist(state.player, {x:state.exit.x+.5,y:state.exit.y+.5});
  const maxD = Math.hypot(COLS/2, ROWS/2);
  const progress = 1 - clamp(d/maxD,0,1);
  if(progress > .78) return 'experto';
  if(progress > .55) return 'avanzado';
  if(progress > .32) return 'medio';
  return 'basico';
}
function difficultyLabel(d){return ({basico:'Básico',medio:'Medio',avanzado:'Avanzado',experto:'Experto',bono:'Bono'})[d] || d;}

function generateMaze(options={}){
  const grid = Array.from({length:ROWS},()=>Array.from({length:COLS},()=> '#'));
  let start = {x:1,y:ROWS-2};
  const exit = options.randomExit ? randomExitCell() : {x:Math.floor(COLS/2), y:Math.floor(ROWS/2)};

  // Laberinto rectangular tipo templo: se genera con DFS sobre celdas impares.
  // Esto garantiza un camino conectado y visible, con corredores amplios en toda la pantalla.
  const stack = [{x:1,y:1}];
  grid[1][1] = '.';
  const dirs = [{x:2,y:0},{x:-2,y:0},{x:0,y:2},{x:0,y:-2}];
  while(stack.length){
    const cur = stack[stack.length-1];
    const choices = shuffle(dirs).map(d=>({x:cur.x+d.x,y:cur.y+d.y,dx:d.x,dy:d.y}))
      .filter(n => n.x>0 && n.y>0 && n.x<COLS-1 && n.y<ROWS-1 && grid[n.y][n.x]==='#');
    if(!choices.length){ stack.pop(); continue; }
    const n = choices[0];
    grid[cur.y+n.dy/2][cur.x+n.dx/2] = '.';
    grid[n.y][n.x] = '.';
    stack.push({x:n.x,y:n.y});
  }

  // Abrir algunos muros internos para que el recorrido sea menos rígido y más jugable.
  for(let y=2;y<ROWS-2;y++){
    for(let x=2;x<COLS-2;x++){
      if(grid[y][x] !== '#') continue;
      const horizontal = grid[y][x-1] === '.' && grid[y][x+1] === '.';
      const vertical = grid[y-1][x] === '.' && grid[y+1][x] === '.';
      if((horizontal || vertical) && Math.random() < (options.randomExit ? 0.16 : 0.10)) grid[y][x] = '.';
    }
  }

  // Cámara central de salida, visible y conectada al laberinto.
  for(let yy=exit.y-1; yy<=exit.y+1; yy++){
    for(let xx=exit.x-1; xx<=exit.x+1; xx++){
      if(xx>0 && yy>0 && xx<COLS-1 && yy<ROWS-1) grid[yy][xx]='.';
    }
  }
  // Conectores de la cámara central hacia el camino cercano.
  for(let x=exit.x-3; x<=exit.x+3; x++) if(x>0 && x<COLS-1) grid[exit.y][x]='.';
  for(let y=exit.y-3; y<=exit.y+3; y++) if(y>0 && y<ROWS-1) grid[y][exit.x]='.';

  // Cámara de entrada inferior izquierda.
  for(let yy=start.y-1; yy<=start.y; yy++){
    for(let xx=start.x; xx<=start.x+2; xx++){
      if(xx>0 && yy>0 && xx<COLS-1 && yy<ROWS-1) grid[yy][xx]='.';
    }
  }

  // Cámaras laterales para tesoros y portales.
  const rooms = [
    {x:7,y:5,w:5,h:3},{x:COLS-12,y:5,w:5,h:3},
    {x:8,y:ROWS-8,w:5,h:3},{x:COLS-13,y:ROWS-8,w:5,h:3},
    {x:Math.floor(COLS/2)-3,y:4,w:7,h:3},{x:Math.floor(COLS/2)-3,y:ROWS-7,w:7,h:3}
  ];
  for(const r of rooms){
    for(let yy=r.y; yy<r.y+r.h; yy++) for(let xx=r.x; xx<r.x+r.w; xx++){
      if(xx>0 && yy>0 && xx<COLS-1 && yy<ROWS-1) grid[yy][xx]='.';
    }
  }

  if(options.farthestStart){
    start = farthestPathFrom(grid, exit);
  }

  grid[start.y][start.x]='S';
  grid[exit.y][exit.x]='E';
  state.grid = grid;
  state.start = start;
  state.exit = exit;
  state.player = {x:start.x+.5,y:start.y+.5};
  configureExitAccessZone();
  state.visitedCell = keyOf(start.x,start.y);
}

function nearestPathTo(grid,target){
  let best=null, bestD=Infinity;
  for(let y=1;y<ROWS-1;y++) for(let x=1;x<COLS-1;x++){
    if(isPathChar(grid[y][x])){
      const d=Math.hypot(x-target.x,y-target.y);
      if(d<bestD){bestD=d; best={x,y};}
    }
  }
  return best || {x:2,y:Math.floor(ROWS/2)};
}
function findOddStart(){
  return state.start || {x:2,y:Math.floor(ROWS/2)};
}
function farthestPathFrom(grid, ref){
  let best=null, bestD=-1;
  for(let y=1;y<ROWS-1;y++){
    for(let x=1;x<COLS-1;x++){
      if(isPathChar(grid[y][x])){
        const d = Math.hypot(x-ref.x, y-ref.y);
        if(d > bestD){ bestD = d; best = {x,y}; }
      }
    }
  }
  return best || {x:1,y:ROWS-2};
}
function randomExitCell(){
  const xChoices = [];
  const yChoices = [];
  for(let x=3; x<COLS-3; x+=2) xChoices.push(x);
  for(let y=3; y<ROWS-3; y+=2) yChoices.push(y);
  return {x:xChoices[randInt(xChoices.length)], y:yChoices[randInt(yChoices.length)]};
}

function chooseExitAccessDirection(){
  const dirs = [
    {x:1,y:0,name:'derecha'}, {x:-1,y:0,name:'izquierda'},
    {x:0,y:1,name:'abajo'}, {x:0,y:-1,name:'arriba'}
  ];
  return dirs
    .filter(d => {
      const x = state.exit.x + d.x * EXIT_ACCESS_CORRIDOR_LENGTH;
      const y = state.exit.y + d.y * EXIT_ACCESS_CORRIDOR_LENGTH;
      return x > 0 && y > 0 && x < COLS - 1 && y < ROWS - 1;
    })
    .sort((a,b) => {
      const da = Math.hypot(state.exit.x + a.x - state.start.x, state.exit.y + a.y - state.start.y);
      const db = Math.hypot(state.exit.x + b.x - state.start.x, state.exit.y + b.y - state.start.y);
      return da - db;
    })[0] || {x:1,y:0,name:'derecha'};
}

function configureExitAccessZone(){
  // Se construye una zona de salida con muchas casillas transportadoras,
  // pero se reserva exactamente una entrada segura cardinal hacia la casilla final.
  const dir = chooseExitAccessDirection();
  const safe = new Set();

  // Abrir una cámara alrededor de la salida para que las casillas transportadoras sean visibles.
  for(let dy=-EXIT_TRANSPORTER_RING_RADIUS; dy<=EXIT_TRANSPORTER_RING_RADIUS; dy++){
    for(let dx=-EXIT_TRANSPORTER_RING_RADIUS; dx<=EXIT_TRANSPORTER_RING_RADIUS; dx++){
      const x = state.exit.x + dx;
      const y = state.exit.y + dy;
      if(x>0 && y>0 && x<COLS-1 && y<ROWS-1 && Math.hypot(dx,dy) <= EXIT_TRANSPORTER_RING_RADIUS + .15){
        state.grid[y][x] = '.';
      }
    }
  }

  // Único corredor seguro: desde la dirección elegida hacia la salida.
  for(let i=1; i<=EXIT_ACCESS_CORRIDOR_LENGTH; i++){
    const x = state.exit.x + dir.x * i;
    const y = state.exit.y + dir.y * i;
    if(x>0 && y>0 && x<COLS-1 && y<ROWS-1){
      state.grid[y][x] = '.';
      safe.add(keyOf(x,y));
    }
  }

  // Tres guardianes matemáticos en el único camino seguro.
  // Se evita poner uno en la casilla inmediatamente pegada a la salida para no bloquear
  // visualmente la entrada final, y se conserva una celda de ingreso al corredor.
  const finalChallenges = new Set();
  const challengePositions = [2,3,4].filter(i => i <= EXIT_ACCESS_CORRIDOR_LENGTH);
  for(const i of challengePositions){
    const x = state.exit.x + dir.x * i;
    const y = state.exit.y + dir.y * i;
    if(x>0 && y>0 && x<COLS-1 && y<ROWS-1){
      finalChallenges.add(keyOf(x,y));
    }
  }

  // Marcar la celda adyacente segura. Cualquier otro acceso cardinal a la salida será transportador.
  state.exitSafeKeys = safe;
  state.finalChallengeCells = finalChallenges;
  state.exitAccessCell = {x: state.exit.x + dir.x, y: state.exit.y + dir.y, dir: dir.name};
  state.grid[state.exit.y][state.exit.x] = 'E';
}

function isExitSafeKey(k){
  return state.exitSafeKeys && state.exitSafeKeys.has(k);
}

function occupiedKeys(){
  const s = new Set([keyOf(state.start.x,state.start.y), keyOf(state.exit.x,state.exit.y), keyOf(Math.floor(state.player.x),Math.floor(state.player.y))]);
  state.treasures.filter(t=>!t.collected).forEach(t=>s.add(keyOf(t.x,t.y)));
  state.portals.forEach(p=>s.add(keyOf(p.x,p.y)));
  state.exitTransporters.forEach(t=>s.add(keyOf(t.x,t.y)));
  if(state.exitSafeKeys) state.exitSafeKeys.forEach(k=>s.add(k));
  if(state.finalChallengeCells) state.finalChallengeCells.forEach(k=>s.add(k));
  state.obstacles.forEach(k=>s.add(k));
  state.bonusCells.forEach(k=>s.add(k));
  state.trapCells.forEach(k=>s.add(k));
  return s;
}
function randomFreeCell({minExit=0,maxExit=999,avoid=null}={}){
  const occ = avoid || occupiedKeys();
  const candidates = pathCells().filter(c => {
    const k=keyOf(c.x,c.y);
    const d=distanceToExitCell(c);
    return !occ.has(k) && d>=minExit && d<=maxExit && isPathChar(state.grid[c.y][c.x]) && state.grid[c.y][c.x] !== 'E' && state.grid[c.y][c.x] !== 'S';
  });
  return candidates[randInt(candidates.length)] || state.start;
}
function placeTreasures(preserveCollected=new Set()){
  state.treasures = [];
  const occ = occupiedKeys();
  for(let i=0;i<TREASURE_TOTAL;i++){
    if(preserveCollected.has(i)){
      state.treasures.push({id:i, icon:TREASURE_ICONS[i], name:TREASURE_NAMES[i], x:-100-i, y:-100-i, collected:true});
      continue;
    }
    const min = 5 + i*2;
    const c = randomFreeCell({minExit:min, avoid:occ});
    occ.add(keyOf(c.x,c.y));
    state.treasures.push({id:i, icon:TREASURE_ICONS[i], name:TREASURE_NAMES[i], x:c.x, y:c.y, collected:false});
  }
}
function relocateTreasure(treasure){
  const occ = occupiedKeys();
  occ.delete(keyOf(treasure.x,treasure.y));
  const c = randomFreeCell({minExit:4, avoid:occ});
  treasure.x = c.x; treasure.y = c.y;
}
function relocateUncollectedTreasures(exceptCollected=true){
  for(const t of state.treasures){
    if(!t.collected || !exceptCollected) relocateTreasure(t);
  }
}
function nearestFreeAround(cell, occ, minR=2, maxR=5){
  const choices=[];
  for(let r=minR;r<=maxR;r++){
    for(let dy=-r;dy<=r;dy++) for(let dx=-r;dx<=r;dx++){
      if(Math.abs(dx)+Math.abs(dy)!==r) continue;
      const x=cell.x+dx,y=cell.y+dy,k=keyOf(x,y);
      if(x>0&&y>0&&x<COLS-1&&y<ROWS-1 && state.grid[y][x] !== '#' && !occ.has(k)) choices.push({x,y});
    }
    if(choices.length) return choices[randInt(choices.length)];
  }
  return null;
}
function placePortals(){
  state.portals = [];
  const occ = occupiedKeys();
  // Los portales normales acompañan a los tesoros, pero nunca se ubican cerca de la salida final.
  const bases = state.treasures.filter(t=>!t.collected && distanceToExitCell(t) >= EXIT_PORTAL_EXCLUSION_RADIUS + 2).map(t=>({x:t.x,y:t.y}));
  let id=0;
  for(const base of bases){
    const p = nearestFreeAround(base, occ, 2, 7);
    if(p && distanceToExitCell(p) >= EXIT_PORTAL_EXCLUSION_RADIUS){
      occ.add(keyOf(p.x,p.y)); state.portals.push({id:id++,x:p.x,y:p.y});
    }
  }
  while(state.portals.length < PORTAL_TOTAL){
    const c=randomFreeCell({minExit:EXIT_PORTAL_EXCLUSION_RADIUS, avoid:occ});
    occ.add(keyOf(c.x,c.y)); state.portals.push({id:id++,x:c.x,y:c.y});
  }
}
function placeExitTransporters(){
  state.exitTransporters = [];
  const occ = occupiedKeys();
  let id = 0;
  const choices=[];

  // Primera prioridad: todas las celdas cardinales y cercanas a la salida,
  // excepto la única celda de acceso seguro. Así solo queda un camino real
  // para entrar a la salida sin activar transporte.
  for(let r=1; r<=EXIT_TRANSPORTER_RING_RADIUS; r++){
    for(let dy=-r; dy<=r; dy++){
      for(let dx=-r; dx<=r; dx++){
        const manhattan = Math.abs(dx)+Math.abs(dy);
        const cheb = Math.max(Math.abs(dx), Math.abs(dy));
        if(cheb !== r) continue;
        const x = state.exit.x + dx;
        const y = state.exit.y + dy;
        const k = keyOf(x,y);
        if(x<=0 || y<=0 || x>=COLS-1 || y>=ROWS-1) continue;
        if(k === keyOf(state.exit.x,state.exit.y)) continue;
        if(isExitSafeKey(k)) continue;
        if(!isPathChar(state.grid[y][x])) continue;
        if(occ.has(k)) continue;
        // Se privilegian las casillas cardinales de radio 1 y luego el anillo externo.
        const priority = (manhattan === 1 ? 0 : r) + Math.random()*.05;
        choices.push({x,y,priority});
      }
    }
  }

  choices.sort((a,b)=>a.priority-b.priority);
  for(const c of choices){
    if(state.exitTransporters.length >= EXIT_TRANSPORTER_TOTAL) break;
    const k = keyOf(c.x,c.y);
    if(occ.has(k) || isExitSafeKey(k)) continue;
    occ.add(k);
    state.exitTransporters.push({id:id++,x:c.x,y:c.y,final:true});
  }

  // Respaldo: si por alguna regeneración faltan transportadores, ponerlos lejos del corredor seguro,
  // pero todavía relativamente cerca de la salida.
  while(state.exitTransporters.length < EXIT_TRANSPORTER_TOTAL){
    const c = randomFreeCell({minExit:2, maxExit:EXIT_TRANSPORTER_RING_RADIUS+3, avoid:occ});
    const k = keyOf(c.x,c.y);
    if(isExitSafeKey(k) || k === keyOf(state.exit.x,state.exit.y)) break;
    occ.add(k);
    state.exitTransporters.push({id:id++,x:c.x,y:c.y,final:true});
  }
}

function placeObstaclesAndBonus(){
  state.obstacles.clear();
  state.bonusCells.clear();
  let occ = occupiedKeys();
  const all = shuffle(pathCells().filter(c => !occ.has(keyOf(c.x,c.y)) && distanceToExitCell(c)>3));
  let obs=0;
  for(const c of all){
    if(obs>=OBSTACLE_TOTAL) break;
    const nearExit = distanceToExitCell(c)<9;
    if(nearExit || Math.random()<0.55){
      const k=keyOf(c.x,c.y);
      state.obstacles.add(k);
      occ.add(k);
      obs++;
    }
  }
  const allBonus = shuffle(pathCells().filter(c => !occ.has(keyOf(c.x,c.y)) && distanceToExitCell(c)>4));
  for(let i=0;i<8 && i<allBonus.length;i++){
    const k=keyOf(allBonus[i].x,allBonus[i].y);
    state.bonusCells.add(k);
    occ.add(k);
  }
}

function placeTrapButtons(){
  state.trapCells.clear();
  let occ = occupiedKeys();
  const cells = shuffle(pathCells().filter(c => {
    const k = keyOf(c.x,c.y);
    const nearExit = distanceToExitCell(c) < 2.4;
    const nearStart = dist(c,state.start) < 2.6;
    return !occ.has(k) && !nearExit && !nearStart && state.grid[c.y][c.x] !== 'E' && state.grid[c.y][c.x] !== 'S';
  }));
  for(const c of cells){
    if(state.trapCells.size >= TRAP_TOTAL) break;
    const k = keyOf(c.x,c.y);
    state.trapCells.add(k);
    occ.add(k);
  }
}
function rebuildLabyrinthAfterTreasureFailure(treasure){
  const collectedIds = new Set(state.treasures.filter(t=>t.collected).map(t=>t.id));
  state.obstacles = new Set();
  state.bonusCells = new Set();
  state.trapCells = new Set();
  state.portals = [];
  state.exitTransporters = [];
  state.exitSafeKeys = new Set();
  state.finalChallengeCells = new Set();
  state.exitAccessCell = null;
  generateMaze({randomExit:true, farthestStart:true});
  placeTreasures(collectedIds);
  placePortals();
  placeExitTransporters();
  placeObstaclesAndBonus();
  placeTrapButtons();
  state.lastQuestionStep = state.steps;
  state.visitedCell = keyOf(Math.floor(state.player.x), Math.floor(state.player.y));
  addEvent(`El reto del tesoro ${treasure.name} fue fallado: el laberinto cambió completamente, la salida se movió y la ficha fue enviada al extremo opuesto.`, 'bad');
  resizeCanvas();
  updateHUD();
}
function rebuildLabyrinthByTrapButton(){
  const collectedIds = new Set(state.treasures.filter(t=>t.collected).map(t=>t.id));
  state.obstacles = new Set();
  state.bonusCells = new Set();
  state.trapCells = new Set();
  state.portals = [];
  state.exitTransporters = [];
  state.exitSafeKeys = new Set();
  state.finalChallengeCells = new Set();
  state.exitAccessCell = null;
  generateMaze({randomExit:true, farthestStart:true});
  placeTreasures(collectedIds);
  placePortals();
  placeExitTransporters();
  placeObstaclesAndBonus();
  placeTrapButtons();
  state.lastQuestionStep = state.steps;
  state.visitedCell = keyOf(Math.floor(state.player.x), Math.floor(state.player.y));
  addEvent('Botón trampa activado: el laberinto cambió completamente de forma y la ficha fue enviada lejos de la nueva salida.', 'trap');
  resizeCanvas();
  updateHUD();
}

function rebuildLabyrinthAfterFinalChallengeFailure(){
  const collectedIds = new Set(state.treasures.filter(t=>t.collected).map(t=>t.id));
  state.obstacles = new Set();
  state.bonusCells = new Set();
  state.trapCells = new Set();
  state.portals = [];
  state.exitTransporters = [];
  state.exitSafeKeys = new Set();
  state.finalChallengeCells = new Set();
  state.exitAccessCell = null;
  generateMaze({randomExit:true, farthestStart:true});
  placeTreasures(collectedIds);
  placePortals();
  placeExitTransporters();
  placeObstaclesAndBonus();
  placeTrapButtons();
  state.lastQuestionStep = state.steps;
  state.visitedCell = keyOf(Math.floor(state.player.x), Math.floor(state.player.y));
  addEvent('Guardián final fallado: perdiste 1.0 unidad, el laberinto cambió completamente y el animal apareció lo más lejos posible de la nueva salida.', 'bad');
  resizeCanvas();
  updateHUD();
}


function resetGame(){
  state.score=1.0; state.steps=0; state.lastQuestionStep=0; state.treasuresFound=0;
  state.answered=[]; state.log=[]; state.startedAt=new Date(); state.finishedAt=null;
  state.security = { locks:0, fullscreenExits:0, focusLosses:0, hiddenTabs:0, escapeKey:0, rightClicks:0, printScreen:0, blockedShortcuts:0, wrongTeacherCodes:0 };
  state.cancelled = false; securityLockActive = false; lastSecurityEventAt = 0;
  state.obstacles = new Set(); state.bonusCells = new Set(); state.trapCells = new Set(); state.portals=[]; state.exitTransporters=[]; state.exitSafeKeys = new Set(); state.finalChallengeCells = new Set(); state.exitAccessCell = null;
  generateMaze();
  placeTreasures();
  placePortals();
  placeExitTransporters();
  placeObstaclesAndBonus();
  placeTrapButtons();
  updateHUD();
  hud.log.innerHTML='';
  addEvent('La expedición comenzó. Encuentra 4 tesoros y luego entra a la salida central. La hora del dispositivo permanecerá visible durante toda la partida.', 'good');
  gameRunning=true; modalOpen=false;
}

function resizeCanvas(){
  const panel = canvas.parentElement;
  const rect = panel.getBoundingClientRect();
  const w = Math.max(320, Math.floor(rect.width));
  const h = Math.max(240, Math.floor(rect.height));
  const dpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));

  canvas.width = Math.floor(w * dpr);
  canvas.height = Math.floor(h * dpr);
  canvas.style.width = `${w}px`;
  canvas.style.height = `${h}px`;
  ctx.setTransform(dpr,0,0,dpr,0,0);

  // El tablero rectangular usa la mayor casilla posible y siempre cabe completo.
  const padX = Math.max(10, Math.floor(w * 0.012));
  const padY = Math.max(10, Math.floor(h * 0.012));
  tile = Math.max(10, Math.floor(Math.min((w - 2*padX) / COLS, (h - 2*padY) / ROWS)));
  offsetX = Math.floor((w - tile * COLS) / 2);
  offsetY = Math.floor((h - tile * ROWS) / 2);
}
window.addEventListener('resize', resizeCanvas);

function draw(){
  const w = canvas.clientWidth, h=canvas.clientHeight;
  ctx.clearRect(0,0,w,h);
  drawChineseBackground(w,h);
  ctx.save();
  ctx.fillStyle='rgba(0,0,0,.18)';
  ctx.fillRect(offsetX-6,offsetY-6,tile*COLS+12,tile*ROWS+12);
  ctx.fillStyle='#9b1c16';
  ctx.fillRect(offsetX,offsetY,tile*COLS,tile*ROWS);
  for(let y=0;y<ROWS;y++) for(let x=0;x<COLS;x++){
    const ch=state.grid[y]?.[x];
    if(ch === '#') drawWall(x,y);
    else if(ch === '.' || ch === 'S' || ch === 'E') drawFloor(x,y);
  }
  for(let y=0;y<ROWS;y++) for(let x=0;x<COLS;x++){
    if(state.grid[y]?.[x] !== '#') drawPathDot(x,y);
  }
  drawSpecials();
  drawPlayer();
  ctx.restore();
  drawOuterFrame();
}
function drawChineseBackground(w,h){
  const g=ctx.createLinearGradient(0,0,0,h);
  g.addColorStop(0,'#1a0707');g.addColorStop(.50,'#43100d');g.addColorStop(1,'#07170d');
  ctx.fillStyle=g;ctx.fillRect(0,0,w,h);
  ctx.save();ctx.globalAlpha=.18;ctx.strokeStyle='#ffd166';ctx.lineWidth=2;
  for(let x=-40;x<w+90;x+=86){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x+44,h);ctx.stroke();ctx.beginPath();ctx.moveTo(x+44,0);ctx.lineTo(x,h);ctx.stroke();}
  ctx.globalAlpha=.14;ctx.font='24px Georgia';ctx.fillStyle='#ffe6a8';
  for(let y=42;y<h;y+=76){for(let x=34;x<w;x+=190){ctx.fillText('龙 门 福 山',x,y);}}
  ctx.restore();
}
function drawFloor(x,y){
  const px=offsetX+x*tile, py=offsetY+y*tile;
  const isGreen = (x+y)%2===0;
  const grd=ctx.createLinearGradient(px,py,px,py+tile);
  // Camino pastel: verde jade claro y rojo coral claro, con alto contraste frente a tesoros y murallas.
  grd.addColorStop(0,isGreen ? '#d8f3dc' : '#ffd6d6');
  grd.addColorStop(.55,isGreen ? '#b7e4c7' : '#ffb8b8');
  grd.addColorStop(1,isGreen ? '#95d5b2' : '#f4a7a7');
  ctx.fillStyle=grd;ctx.fillRect(px,py,tile,tile);
  ctx.strokeStyle=isGreen ? 'rgba(38,112,83,.22)' : 'rgba(154,49,49,.22)';
  ctx.lineWidth=Math.max(1,tile*.035);ctx.strokeRect(px+.5,py+.5,tile-1,tile-1);
  if(tile >= 18){
    ctx.save();
    ctx.globalAlpha=.18;
    ctx.strokeStyle=isGreen ? '#2d8f6f' : '#b85c5c';
    ctx.lineWidth=Math.max(1,tile*.025);
    ctx.beginPath();
    ctx.moveTo(px+tile*.18,py+tile*.78);ctx.lineTo(px+tile*.82,py+tile*.22);
    ctx.stroke();
    ctx.restore();
  }
}
function drawPathDot(x,y){
  const px=offsetX+(x+.5)*tile, py=offsetY+(y+.5)*tile;
  if((x+y)%6===0){
    ctx.fillStyle='rgba(255,255,255,.34)';
    ctx.beginPath();ctx.arc(px,py,Math.max(1.4,tile*.055),0,Math.PI*2);ctx.fill();
  }
}
function drawWall(x,y){
  const px=offsetX+x*tile, py=offsetY+y*tile;
  const grd=ctx.createLinearGradient(px,py,px+tile,py+tile);
  grd.addColorStop(0,'#8fc9a3');grd.addColorStop(.50,'#5ca985');grd.addColorStop(1,'#2f6f58');
  ctx.fillStyle=grd;ctx.fillRect(px,py,tile,tile);
  ctx.strokeStyle='rgba(255,232,154,.64)';ctx.lineWidth=Math.max(1,tile*.045);ctx.strokeRect(px+1,py+1,tile-2,tile-2);
  if(tile >= 24 && (x+y)%7===0){
    ctx.fillStyle='rgba(255,250,218,.44)';ctx.font=`${Math.max(8,tile*.32)}px serif`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText('福',px+tile/2,py+tile*.55);
  }
}
function drawSpecials(){
  // salida central
  const exitOpen = state.treasuresFound >= TREASURE_TOTAL;
  drawIconCell(state.exit.x,state.exit.y, exitOpen?'🏯':'🔒', exitOpen?'#ffd166':'#493219', exitOpen?'#3a0b07':'#ffd35a');
  state.exitTransporters.forEach(t=>drawIconCell(t.x,t.y,EXIT_TRANSPORTER_ICON,'#0f6b4d','#fff3ce',true));
  if(state.finalChallengeCells){ state.finalChallengeCells.forEach(k=>{ const [x,y]=k.split(',').map(Number); drawIconCell(x,y,FINAL_CHALLENGE_ICON,'#7a1111','#ffe38a',true); }); }
  state.portals.forEach(p=>drawIconCell(p.x,p.y,PORTAL_ICON,'#6436e8','#fff'));
  let obstacleIndex = 0;
  state.obstacles.forEach(k=>{const [x,y]=k.split(',').map(Number); drawIconCell(x,y,OBSTACLE_ICONS[obstacleIndex++ % OBSTACLE_ICONS.length],'#5c1b16','#ffd35a');});
  state.bonusCells.forEach(k=>{const [x,y]=k.split(',').map(Number); drawIconCell(x,y,BONUS_ICON,'#9b1c16','#ffe6a8');});
  state.trapCells.forEach(k=>{const [x,y]=k.split(',').map(Number); drawIconCell(x,y,TRAP_ICON,'#c6281e','#fff3ce',true);});
  state.treasures.filter(t=>!t.collected).forEach(t=>drawTreasureCell(t.x,t.y,t.icon,t.name));
}
function drawTreasureCell(x,y,icon,name='Tesoro'){
  const px=offsetX+x*tile, py=offsetY+y*tile;
  const cx=px+tile/2, cy=py+tile/2;
  ctx.save();

  // Halo exterior grande: hace que el tesoro se vea distinto incluso en tableros pequeños.
  const halo=ctx.createRadialGradient(cx,cy,tile*.08,cx,cy,tile*1.15);
  halo.addColorStop(0,'rgba(255,255,205,.96)');
  halo.addColorStop(.28,'rgba(255,224,102,.72)');
  halo.addColorStop(.58,'rgba(255,140,80,.34)');
  halo.addColorStop(1,'rgba(255,224,102,0)');
  ctx.fillStyle=halo;
  ctx.beginPath();ctx.arc(cx,cy,tile*1.05,0,Math.PI*2);ctx.fill();

  // Rayos dorados alrededor de la casilla.
  ctx.strokeStyle='rgba(255,247,183,.92)';
  ctx.lineWidth=Math.max(1.2,tile*.055);
  for(let i=0;i<12;i++){
    const a=(Math.PI*2*i)/12;
    const r1=tile*.48, r2=tile*.69;
    ctx.beginPath();
    ctx.moveTo(cx+Math.cos(a)*r1,cy+Math.sin(a)*r1);
    ctx.lineTo(cx+Math.cos(a)*r2,cy+Math.sin(a)*r2);
    ctx.stroke();
  }

  ctx.shadowColor='rgba(255,225,86,.98)';
  ctx.shadowBlur=Math.max(20,tile*.95);
  const grd=ctx.createLinearGradient(px,py,px+tile,py+tile);
  grd.addColorStop(0,'#fffbd1');
  grd.addColorStop(.45,'#ffd54d');
  grd.addColorStop(1,'#ff8f3d');
  ctx.fillStyle=grd;
  ctx.beginPath();ctx.roundRect(px+tile*.06,py+tile*.06,tile*.88,tile*.88,tile*.22);ctx.fill();
  ctx.shadowBlur=0;

  ctx.strokeStyle='#fff8b0';ctx.lineWidth=Math.max(2,tile*.09);ctx.stroke();
  ctx.strokeStyle='#9b1c16';ctx.lineWidth=Math.max(1.2,tile*.045);ctx.strokeRect(px+tile*.10,py+tile*.10,tile*.80,tile*.80);

  // Medallón blanco central para que el icono no se confunda con el camino pastel.
  ctx.fillStyle='rgba(255,255,245,.92)';
  ctx.beginPath();ctx.arc(cx,cy,tile*.33,0,Math.PI*2);ctx.fill();
  ctx.fillStyle='#421507';ctx.textAlign='center';ctx.textBaseline='middle';
  ctx.font=`${Math.max(14,tile*.68)}px serif`;ctx.fillText(icon || '🏮',cx,cy+tile*.02);

  if(tile >= 24){
    ctx.font=`${Math.max(7,tile*.18)}px system-ui, sans-serif`;
    ctx.fillStyle='#7a1111';
    ctx.fillText('TESORO',cx,py+tile*.91);
  }
  ctx.restore();
}
function drawIconCell(x,y,icon,bg,fg,glow=false){
  const px=offsetX+x*tile, py=offsetY+y*tile;
  ctx.save();
  if(glow){ctx.shadowColor='#ffe27a';ctx.shadowBlur=18;}
  ctx.fillStyle=bg;ctx.beginPath();ctx.roundRect(px+tile*.13,py+tile*.13,tile*.74,tile*.74,tile*.18);ctx.fill();
  ctx.shadowBlur=0;ctx.fillStyle=fg;ctx.textAlign='center';ctx.textBaseline='middle';ctx.font=`${Math.max(12,tile*.58)}px serif`;ctx.fillText(icon || '福',px+tile/2,py+tile*.53);
  ctx.restore();
}
function drawPlayer(){
  const px=offsetX+state.player.x*tile, py=offsetY+state.player.y*tile;
  ctx.save();
  ctx.shadowColor='rgba(255,211,90,.85)';ctx.shadowBlur=14;
  ctx.fillStyle='#fff3ce';ctx.beginPath();ctx.arc(px,py,tile*.43,0,Math.PI*2);ctx.fill();
  ctx.shadowBlur=0;ctx.textAlign='center';ctx.textBaseline='middle';ctx.font=`${Math.max(18,tile*.75)}px serif`;ctx.fillText(selectedAnimal,px,py+tile*.02);
  ctx.restore();
}
function drawOuterFrame(){
  ctx.save();
  const x = offsetX, y = offsetY, w = tile*COLS, h = tile*ROWS;
  ctx.shadowColor='#00d5c8';ctx.shadowBlur=18;
  ctx.strokeStyle='#ffd35a';ctx.lineWidth=Math.max(4,tile*.20);
  ctx.strokeRect(x,y,w,h);
  ctx.shadowBlur=0;
  ctx.strokeStyle='rgba(255,243,206,.78)';ctx.lineWidth=Math.max(1,tile*.045);
  ctx.strokeRect(x+tile*.45,y+tile*.45,w-tile*.9,h-tile*.9);
  ctx.restore();
}

function gameLoop(now){
  const dt = Math.min(.05,(now-lastTime)/1000);
  lastTime=now;
  if(gameRunning && !modalOpen){ updatePlayer(dt); }
  draw();
  requestAnimationFrame(gameLoop);
}
requestAnimationFrame(gameLoop);

function updatePlayer(dt){
  const dir = getActiveDir();
  currentDir = dir;
  if(dir.x===0 && dir.y===0) return;
  const speed = SPEED_CELLS_PER_SEC * dt;
  let nx = state.player.x + dir.x*speed;
  let ny = state.player.y + dir.y*speed;
  // colisión por ejes para deslizar suave
  if(isFreeAt(nx,state.player.y)) state.player.x = nx;
  if(isFreeAt(state.player.x,ny)) state.player.y = ny;
  const c = cellOf(state.player);
  const ck = keyOf(c.x,c.y);
  if(ck !== state.visitedCell){
    state.visitedCell=ck;
    state.steps++;
    handleCell(c);
    updateHUD();
  }
}
function getActiveDir(){
  // prioridad a la última tecla pulsada entre las que siguen presionadas
  const order = Array.from(keys).reverse();
  for(const k of order){ if(keyToDir[k]) return keyToDir[k]; }
  return {x:0,y:0};
}
function handleCell(c){
  const k=keyOf(c.x,c.y);
  const treasure = state.treasures.find(t=>!t.collected && t.x===c.x && t.y===c.y);
  if(treasure){ openQuestion('treasure', treasure); return; }
  const exitTransporter = state.exitTransporters.find(t=>t.x===c.x && t.y===c.y);
  if(exitTransporter){ teleportFromExitTransporter(exitTransporter); return; }
  const portal = state.portals.find(p=>p.x===c.x && p.y===c.y);
  if(portal){ teleportFrom(portal); return; }
  if(state.obstacles.has(k)){ openQuestion('obstacle', {key:k}); return; }
  if(state.bonusCells.has(k)){ openQuestion('bonus', {key:k}); return; }
  if(state.trapCells.has(k)){ rebuildLabyrinthByTrapButton(); return; }
  if(state.finalChallengeCells && state.finalChallengeCells.has(k)){ openQuestion('finalChallenge', {key:k}); return; }
  if(c.x===state.exit.x && c.y===state.exit.y){
    if(state.treasuresFound >= TREASURE_TOTAL){ state.score = MAX_SCORE; updateHUD(); finishGame('Has encontrado los cuatro tesoros y llegaste a la puerta central. Nota final: 5.0.'); }
    else { addEvent(`La puerta de salida está cerrada. Faltan ${TREASURE_TOTAL-state.treasuresFound} tesoros.`, 'bad'); }
    return;
  }
  if(state.steps>0 && state.steps % QUESTION_STEP_INTERVAL === 0 && state.lastQuestionStep !== state.steps){
    state.lastQuestionStep = state.steps;
    openQuestion('regular', {});
  }
}
function teleportFromExitTransporter(transporter){
  // Los transportadores alrededor de la salida castigan accesos equivocados:
  // envían a una cámara lejana de la salida, no a otro portal cercano.
  const candidates = pathCells().filter(c => {
    const k = keyOf(c.x,c.y);
    return distanceToExitCell(c) >= Math.max(12, Math.floor(COLS/3))
      && !state.trapCells.has(k)
      && !state.obstacles.has(k)
      && !state.bonusCells.has(k)
      && !state.treasures.some(t => !t.collected && t.x===c.x && t.y===c.y)
      && !state.portals.some(p => p.x===c.x && p.y===c.y);
  });
  const target = candidates[randInt(candidates.length)] || state.start;
  addEvent('Transportador final activado: el animal fue enviado lejos de la salida. Busca el único corredor seguro para entrar.', 'portal');
  state.player.x = target.x + .5;
  state.player.y = target.y + .5;
  state.visitedCell = keyOf(target.x,target.y);
}

function teleportFrom(portal){
  if(state.portals.length<2) return;
  const others = state.portals.filter(p=>p.id!==portal.id);
  const target = others[randInt(others.length)];
  addEvent(`Portal activado: el animal fue transportado a otra cámara del laberinto.`, 'portal');
  state.player.x = target.x+.5; state.player.y=target.y+.5; state.visitedCell=keyOf(target.x,target.y);
}

function openQuestion(kind, data){
  modalOpen = true;
  let difficulty = kind==='bonus' ? 'bono' : difficultyAtPlayer();
  if(kind==='treasure') difficulty = 'experto';
  if(kind==='finalChallenge') difficulty = 'avanzado';
  if(kind==='obstacle' && difficulty==='basico') difficulty='medio';
  const q = chooseQuestion(difficulty, kind);
  activeQuestion = {kind, data, q};
  currentAnswerResult = null; pendingAfterQuestion = null;
  questionBadge.textContent = difficultyLabel(q.difficulty === 'bono' ? 'bono' : difficulty);
  questionTitle.textContent = buildQuestionTitle(kind, q);
  questionText.innerHTML = `<div class="topic"><strong>Tema:</strong> ${q.topic}</div><div class="latex-panel">${q.prompt}</div>`;
  if(kind === 'treasure'){
    hintBtn.classList.add('hidden');
    hintText.innerHTML = `<strong>Reto de tesoro:</strong><div class="latex-panel small-latex">Este reto no tiene pista. Debe resolverse con el procedimiento matemático completo.</div>`;
  } else if(kind === 'finalChallenge'){
    hintBtn.classList.add('hidden');
    hintText.innerHTML = `<strong>Guardián final:</strong><div class="latex-panel small-latex">Este reto avanzado no tiene pista. Si fallas, perderás \(1.0\) unidad y el laberinto cambiará completamente.</div>`;
  } else {
    hintBtn.classList.remove('hidden');
    hintText.innerHTML = `<strong>Pista orientadora:</strong><div class="latex-panel small-latex">${q.hint}</div>`;
  }
  hintText.classList.add('hidden');
  feedbackBox.className='feedback hidden math-book'; feedbackBox.innerHTML='';
  submitAnswerBtn.classList.remove('hidden'); continueBtn.classList.add('hidden');
  renderAnswerForm(q);
  questionModal.classList.remove('hidden');
  typesetMath();
}
function buildQuestionTitle(kind,q){
  if(kind==='treasure') return `Reto del tesoro: ${activeQuestion?.data?.name || 'tesoro'}`;
  if(kind==='finalChallenge') return 'Guardián final del corredor seguro';
  if(kind==='obstacle') return 'Muralla de reto';
  if(kind==='bonus') return q.title;
  return q.title;
}
function chooseQuestion(difficulty, kind){
  const targetDifficulty = kind === 'bonus' ? 'bono' : (kind === 'treasure' ? 'experto' : (kind === 'finalChallenge' ? 'avanzado' : difficulty));
  const used = new Set(state.answered.slice(-120).map(a=>a.id));
  const types = (kind === 'treasure' || kind === 'finalChallenge') ? ['statements','integer','choice'] : (questionBank.types || ['tf','statements','integer','choice']);

  // Muestreo pseudoaleatorio sin preconstruir el banco completo.
  // Se prueban varios índices hasta encontrar una pregunta con la dificultad pedida
  // y que no haya aparecido recientemente.
  for(let attempt=0; attempt<220; attempt++){
    const type = types[randInt(types.length)];
    const i = randInt(QUESTIONS_PER_TYPE);
    const q = makeGeneratedQuestion(type, i);
    if(q.difficulty === targetDifficulty && !used.has(q.id)) return q;
  }

  // Respaldo determinístico: garantiza que siempre haya pregunta disponible
  // aunque el azar no encuentre una coincidencia en los intentos anteriores.
  const fallbackStart = randInt(QUESTIONS_PER_TYPE);
  for(const type of shuffle(types.slice())){
    for(let step=0; step<QUESTIONS_PER_TYPE; step++){
      const i = (fallbackStart + step) % QUESTIONS_PER_TYPE;
      const q = makeGeneratedQuestion(type, i);
      if(q.difficulty === targetDifficulty && !used.has(q.id)) return q;
    }
  }

  // Último respaldo: una pregunta media, para evitar que el juego se bloquee.
  for(const type of types){
    for(let i=0; i<25; i++){
      const q = makeGeneratedQuestion(type, i);
      if(q.difficulty === 'medio') return q;
    }
  }
  return makeGeneratedQuestion('choice', 1);
}
function renderAnswerForm(q){
  answerForm.innerHTML='';
  if(q.type==='integer'){
    answerForm.innerHTML = `<label class="integer-answer"><span>Respuesta entera:</span><input id="integerInput" type="number" step="1" autocomplete="off" placeholder="Ejemplo: 3" /></label>`;
    setTimeout(()=>document.getElementById('integerInput')?.focus(),50);
    return;
  }
  q.options.forEach((op,i)=>{
    const id=`op_${i}`;
    const label=document.createElement('label');
    label.className='answer-option math-book';
    label.innerHTML=`<input type="radio" name="answer" value="${escapeAttr(op)}" id="${id}"><span class="option-text">${op}</span>`;
    answerForm.appendChild(label);
  });
}
function escapeAttr(s){ return String(s).replaceAll('&','&amp;').replaceAll('"','&quot;').replaceAll('<','&lt;').replaceAll('>','&gt;'); }
function getUserAnswer(q){
  if(q.type==='integer') return (document.getElementById('integerInput')?.value || '').trim();
  return answerForm.querySelector('input[name="answer"]:checked')?.value || '';
}
function submitAnswer(){
  if(!activeQuestion) return;
  const q = activeQuestion.q;
  const user = getUserAnswer(q);
  if(user===''){ alert('Selecciona o escribe una respuesta antes de continuar.'); return; }
  const correct = q.type==='integer' ? String(parseInt(user,10)) === String(q.answer) : user === q.answer;
  const delta = scoreDelta(activeQuestion.kind, correct);
  state.score = clamp(Number((state.score + delta).toFixed(2)), 0, MAX_SCORE);
  const feedbackKind = correct ? 'good' : 'bad';
  feedbackBox.className = `feedback ${feedbackKind} math-book`;
  feedbackBox.innerHTML = buildFeedback(q,user,correct,delta);
  submitAnswerBtn.classList.add('hidden'); continueBtn.classList.remove('hidden');
  state.answered.push({
    id:q.id, title:q.title, topic:q.topic, difficulty:q.difficulty, kind:activeQuestion.kind,
    user, correct, delta, solution:q.solution, prompt:q.prompt, answer:q.answer, hint:(activeQuestion.kind==='treasure' || activeQuestion.kind==='finalChallenge') ? '' : q.hint, type:q.type
  });
  prepareAfterQuestion(correct);
  updateHUD();
  typesetMath();
}
function scoreDelta(kind,correct){
  if(kind==='treasure') return correct ? 1.0 : -0.5;
  if(kind==='finalChallenge') return correct ? 0.2 : -1.0;
  if(kind==='bonus') return correct ? 0.3 : 0;
  return correct ? 0.2 : -0.1;
}
function buildFeedback(q,user,correct,delta){
  const ans = q.type==='integer' ? q.answer : q.answer;
  const change = `${delta>=0?'+':''}${delta.toFixed(1)}`;
  if(correct){
    return `<div class="feedback-title">Respuesta correcta · cambio en la nota: ${change}</div>
      <div class="solution-block latex-panel"><h3>Procedimiento matemático</h3><p>${q.solution}</p></div>`;
  }
  return `<div class="feedback-title">Respuesta incorrecta · cambio en la nota: ${change}</div>
    <p>Tu respuesta fue <em>${escapeHtml(user)}</em>, pero la respuesta correcta era <strong>${escapeHtml(ans)}</strong>.</p>
    <div class="solution-block latex-panel"><h3>Por qué era incorrecta y cómo debía hacerse</h3><p>${q.solution}</p></div>`;
}
function escapeHtml(s){return String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;');}
function prepareAfterQuestion(correct){
  const {kind,data} = activeQuestion;
  if(kind==='treasure'){
    pendingAfterQuestion = () => {
      if(correct){
        data.collected = true;
        state.treasuresFound++;
        addEvent(`Tesoro encontrado: ${data.name}. Ganaste +1.0 unidad.`, 'treasure');
      } else {
        rebuildLabyrinthAfterTreasureFailure(data);
        return;
      }
      relocateUncollectedTreasures(true);
      placePortals();
      updateHUD();
    };
  } else if(kind==='finalChallenge'){
    pendingAfterQuestion = () => {
      if(correct){
        state.finalChallengeCells.delete(data.key);
        addEvent('Guardián final superado: el corredor seguro queda abierto en esa casilla.', 'good');
      } else {
        rebuildLabyrinthAfterFinalChallengeFailure();
      }
      updateHUD();
    };
  } else if(kind==='obstacle'){
    pendingAfterQuestion = () => {
      state.obstacles.delete(data.key);
      addEvent(correct ? 'Superaste una muralla de reto.' : 'La muralla quedó resuelta, pero la respuesta fue incorrecta.', correct?'good':'bad');
    };
  } else if(kind==='bonus'){
    pendingAfterQuestion = () => {
      state.bonusCells.delete(data.key);
      addEvent(correct ? 'Bono del templo logrado: suma adicional.' : 'Bono del templo fallado: no resta nota.', correct?'bonus':'bad');
    };
  } else {
    pendingAfterQuestion = () => addEvent(correct ? 'Pregunta regular correcta.' : 'Pregunta regular incorrecta.', correct?'good':'bad');
  }
}
function continueAfterQuestion(){
  questionModal.classList.add('hidden');
  if(pendingAfterQuestion) pendingAfterQuestion();
  activeQuestion=null; pendingAfterQuestion=null; modalOpen=false;
}
function typesetMath(){ if(window.MathJax?.typesetPromise) MathJax.typesetPromise().catch(()=>{}); }

function updateHUD(){
  updateDeviceClock();
  hud.score.textContent = state.score.toFixed(1);
  hud.treasure.textContent = `${state.treasuresFound}/${TREASURE_TOTAL}`;
  hud.steps.textContent = state.steps;
  const diff = difficultyAtPlayer();
  hud.difficulty.textContent = difficultyLabel(diff);
  const remaining = TREASURE_TOTAL-state.treasuresFound;
  hud.mission.textContent = remaining>0 ? `Faltan ${remaining} tesoro${remaining===1?'':'s'}. Encuéntralos antes de entrar a la puerta central.` : 'Los cuatro tesoros han sido encontrados. La puerta final está abierta: entra por el único corredor seguro y supera sus tres guardianes avanzados; las otras casillas cercanas transportan lejos.';
}
function addEvent(text,type=''){
  state.log.unshift({time:new Date(),text,type});
  state.log = state.log.slice(0,60);
  renderLog();
}
function renderLog(){
  hud.log.innerHTML = state.log.slice(0,12).map(e=>`<div class="event ${e.type}"><strong>${e.time.toLocaleTimeString()}</strong><br>${escapeHtml(e.text)}</div>`).join('');
}

function finishGame(message='La travesía ha finalizado.'){
  gameRunning=false; modalOpen=true; state.finishedAt=new Date();
  endTitle.textContent = message;
  const correct = state.answered.filter(a=>a.correct).length;
  const total = state.answered.length;
  endSummary.innerHTML = `
    <p>Resultado de la travesía en el laberinto chino.</p>
    <table>
      <tr><th>Nota final</th><td>${state.score.toFixed(1)}</td></tr>
      <tr><th>Tesoros encontrados</th><td>${state.treasuresFound}/${TREASURE_TOTAL}</td></tr>
      <tr><th>Preguntas respondidas</th><td>${total}</td></tr>
      <tr><th>Aciertos</th><td>${correct}</td></tr>
      <tr><th>Pasos</th><td>${state.steps}</td></tr>
      <tr><th>Bloqueos de seguridad</th><td>${state.security?.locks || 0}/${MAX_SECURITY_LOCKS}</td></tr>
    </table>
    <p>El informe HTML incluye portada, resumen, gráficas de desempeño, fórmulas para repasar, plan de mejora, registro de eventos y detalle de cada pregunta con procedimiento matemático.</p>`;
  endModal.classList.remove('hidden');
  typesetMath();
}
function generateReport(){
  const finished = state.finishedAt || new Date();
  const total = state.answered.length;
  const correct = state.answered.filter(a=>a.correct).length;
  const incorrect = total - correct;
  const pct = total ? Math.round((correct/total)*100) : 0;
  const treasurePct = Math.round((state.treasuresFound/TREASURE_TOTAL)*100);
  const elapsedMs = Math.max(0, finished - (state.startedAt || finished));
  const elapsedMin = Math.floor(elapsedMs/60000);
  const elapsedSec = Math.floor((elapsedMs%60000)/1000);
  const resultLabel = state.cancelled ? 'Quiz anulado por eventos críticos de seguridad' : (state.treasuresFound >= TREASURE_TOTAL ? 'Expedición completada' : 'Expedición en progreso o finalizada manualmente');
  const score50 = Math.max(0, Math.min(50, Math.round(state.score*10)));

  const byTopic = {};
  const byType = {};
  const byDifficulty = {};
  const allTopics = ['Sucesiones','Series numéricas','Serie geométrica','Serie p-armónica','Prueba del término general','Criterio de la razón','Criterio de la raíz','Comparación al límite','Criterio integral','Series telescópicas'];
  for(const topic of allTopics) byTopic[topic] = {ok:0,total:0};
  for(const a of state.answered){
    const topic = a.topic || 'Sin tema';
    if(!byTopic[topic]) byTopic[topic] = {ok:0,total:0};
    byTopic[topic].total++;
    if(a.correct) byTopic[topic].ok++;
    const typeName = questionTypeLabel(a.type);
    if(!byType[typeName]) byType[typeName] = {ok:0,total:0};
    byType[typeName].total++;
    if(a.correct) byType[typeName].ok++;
    const diffName = difficultyLabel(a.difficulty || 'basico');
    if(!byDifficulty[diffName]) byDifficulty[diffName] = {ok:0,total:0};
    byDifficulty[diffName].total++;
    if(a.correct) byDifficulty[diffName].ok++;
  }

  function statRows(obj){
    const entries = Object.entries(obj).filter(([_,v])=>v.total>0);
    if(!entries.length) return '<p class="muted">Aún no hay preguntas respondidas para graficar desempeño.</p>';
    return entries.map(([name,v])=>{
      const p = v.total ? Math.round((v.ok/v.total)*100) : 0;
      return `<div class="bar-row"><div class="bar-label"><strong>${escapeHtml(name)}</strong><span>${v.ok}/${v.total} · ${p}%</span></div><div class="bar-track"><div class="bar-fill" style="width:${p}%"></div></div></div>`;
    }).join('');
  }
  function formulaCards(){
    const cards = [
      {t:'Sucesiones racionales', r:'Límite por coeficientes principales', f:'\\[\\lim_{n\\to\\infty}\\frac{an+b}{cn+d}=\\frac{a}{c}\\]', m:'Compara grados y divide por la potencia dominante de n.', e:'Sustituir un valor particular de n como si fuera el límite.'},
      {t:'Serie geométrica', r:'Razón común', f:'\\[\\sum_{n=0}^{\\infty}r^n\\text{ converge si }|r|<1\\]', m:'Identifica la razón común antes de concluir.', e:'Pensar que una potencia pequeña garantiza convergencia sin revisar |r|.'},
      {t:'Serie p-armónica', r:'Exponente crítico', f:'\\[\\sum_{n=1}^{\\infty}\\frac{1}{n^p}\\text{ converge si }p>1\\]', m:'Compara el exponente con 1.', e:'Confundir el caso p=1 con un caso convergente.'},
      {t:'Criterio de la razón', r:'Cociente consecutivo', f:'\\[L=\\lim_{n\\to\\infty}\\left|\\frac{a_{n+1}}{a_n}\\right|\\]', m:'Si L<1 converge; si L>1 diverge; si L=1 no decide.', e:'Olvidar simplificar factoriales o potencias antes de tomar el límite.'},
      {t:'Criterio de la raíz', r:'Raíz n-ésima', f:'\\[L=\\lim_{n\\to\\infty}\\sqrt[n]{|a_n|}\\]', m:'Úsalo cuando el término general contiene potencias n.', e:'No separar factores que tienden a 1.'},
      {t:'Comparación al límite', r:'Cociente con una serie conocida', f:'\\[\\lim_{n\\to\\infty}\\frac{a_n}{b_n}=c,\\quad 0<c<\\infty\\]', m:'Escoge b_n según la potencia dominante.', e:'Usar una comparación cuyo límite no sea positivo y finito sin justificar.'},
      {t:'Criterio integral', r:'Integral impropia asociada', f:'\\[\\sum f(n)\\quad\\leftrightarrow\\quad\\int f(x)\\,dx\\]', m:'Verifica positividad, continuidad y decrecimiento eventual.', e:'Aplicarlo sin revisar las hipótesis de la función.'}
    ];
    return cards.map(c=>`<article class="formula-card"><h3>${c.t}</h3><p><strong>${c.r}:</strong></p><div class="formula">${c.f}</div><p><strong>Método recomendado:</strong> ${c.m}</p><p><strong>Error frecuente:</strong> ${c.e}</p></article>`).join('');
  }
  function improvementPlan(){
    const weak = Object.entries(byTopic).filter(([_,v])=>v.total>0).sort((a,b)=>((a[1].ok/a[1].total)-(b[1].ok/b[1].total))).slice(0,4);
    if(!weak.length) return '<p class="muted">No hay suficientes respuestas para construir un plan de mejora individual.</p>';
    return `<ol>${weak.map(([name,v])=>{
      const p = Math.round((v.ok/v.total)*100);
      return `<li><strong>${escapeHtml(name)}:</strong> ${v.ok}/${v.total} · ${p}%. Revisar definición, fórmula central, procedimiento de sustitución y verificación de extremos o coeficientes según corresponda.</li>`;
    }).join('')}</ol>`;
  }
  function eventTable(){
    const sec = state.security || {};
    return `<table class="security-table"><tr><th>Evento</th><th>Cantidad</th></tr>
      <tr><td>Bloqueos de seguridad activados</td><td>${sec.locks||0}/${MAX_SECURITY_LOCKS}</td></tr>
      <tr><td>Salidas de pantalla completa registradas</td><td>${sec.fullscreenExits||0}</td></tr>
      <tr><td>Cambios de ventana o pérdida de foco</td><td>${sec.focusLosses||0}</td></tr>
      <tr><td>Pestaña oculta o minimización</td><td>${sec.hiddenTabs||0}</td></tr>
      <tr><td>Uso de tecla Escape</td><td>${sec.escapeKey||0}</td></tr>
      <tr><td>Intentos de pantallazo / impresión</td><td>${sec.printScreen||0}</td></tr>
      <tr><td>Atajos bloqueados</td><td>${sec.blockedShortcuts||0}</td></tr>
      <tr><td>Clic derecho bloqueado</td><td>${sec.rightClicks||0}</td></tr>
      <tr><td>Códigos docentes incorrectos</td><td>${sec.wrongTeacherCodes||0}</td></tr>
      <tr><td>Portales y transportadores activados</td><td>${state.log.filter(e=>e.type==='portal').length}</td></tr>
      <tr><td>Botones trampa activados</td><td>${state.log.filter(e=>e.type==='trap').length}</td></tr>
      <tr><td>Obstáculos configurados por laberinto</td><td>${OBSTACLE_TOTAL}</td></tr>
      <tr><td>Portales configurados por laberinto</td><td>${PORTAL_TOTAL}</td></tr>
      <tr><td>Botones trampa configurados por laberinto</td><td>${TRAP_TOTAL}</td></tr>
      <tr><td>Eventos registrados en bitácora</td><td>${state.log.length}</td></tr>
    </table>`;
  }
  function answerComparison(a){
    if(a.type === 'statements'){
      const expected = String(a.answer||'').split(/,| y /).map(x=>x.trim()).filter(Boolean);
      const userParts = String(a.user||'').split(/,| y /).map(x=>x.trim()).filter(Boolean);
      return `<div class="comparison-list"><p><strong>Comparación afirmación por afirmación:</strong></p>${['I','II','III'].map(mark=>{
        const ok = expected.includes(mark);
        const marked = userParts.includes(mark) || String(a.user).includes(mark);
        const good = ok===marked;
        return `<div class="mini-check ${good?'yes':'no'}"><strong>${good?'✓':'✗'} ${mark}.</strong> Valor correcto: ${ok?'verdadera, debía marcarse':'falsa, no debía marcarse'}. En tu respuesta: ${marked?'la marcaste':'no la marcaste'}.</div>`;
      }).join('')}</div>`;
    }
    return `<div class="comparison-list"><div class="mini-check ${a.correct?'yes':'no'}"><strong>${a.correct?'✓':'✗'} Comparación:</strong> tu respuesta fue ${escapeHtml(a.user)} y la respuesta esperada era ${escapeHtml(a.answer)}.</div></div>`;
  }
  function detailedQuestions(){
    if(!state.answered.length) return '<p class="muted">No se respondieron preguntas durante esta expedición.</p>';
    return state.answered.map((a,i)=>`
      <article class="question-card">
        <div class="question-top"><span class="num">${i+1}</span><div><h3>${escapeHtml(a.title)} · ${escapeHtml(a.topic)}</h3><p>${kindLabel(a.kind)} · ${questionTypeLabel(a.type)} · ${difficultyLabel(a.difficulty)}</p></div><span class="pill ${a.correct?'ok':'bad'}">${a.correct?'Correcta':'Incorrecta'}</span></div>
        <div class="twocol"><div class="answer-box"><strong>Respuesta del estudiante</strong><p>${escapeHtml(a.user)}</p></div><div class="answer-box"><strong>Respuesta correcta</strong><p>${escapeHtml(a.answer)}</p></div></div>
        <div class="feedback-panel">
          <h4>Retroalimentación específica de esta pregunta</h4>
          <div class="subcard"><strong>Pregunta respondida:</strong><div class="formula">${a.prompt}</div></div>
          <div class="subcard"><strong>Pista disponible:</strong><p>${a.kind==='treasure' ? 'Este reto de tesoro no tenía pista disponible.' : (a.kind==='finalChallenge' ? 'Este guardián final no tenía pista disponible.' : (a.hint || 'Revisar la fórmula central y sustituir con cuidado.'))}</p></div>
          <div class="subcard"><strong>Diagnóstico:</strong><p>${a.correct ? 'Tu procedimiento coincide con la idea central del ejercicio.' : 'Tu respuesta no coincide con la respuesta esperada. El error suele estar en la identificación del centro, el radio, el extremo, el signo, el coeficiente o la reindexación de la serie.'}</p></div>
          <div class="subcard">${answerComparison(a)}</div>
          <div class="subcard"><strong>Pasos necesarios:</strong><ol><li>Identifica la fórmula o serie base que corresponde al problema.</li><li>Sustituye el centro, el coeficiente o el valor indicado sin cambiar la estructura de la serie.</li><li>Aplica sucesiones, serie geométrica, prueba del término general, razón, raíz, comparación al límite o criterio integral según el caso.</li><li>Concluye exactamente lo que pide la pregunta y verifica si se requiere revisar extremos.</li></ol></div>
          <div class="subcard"><strong>Procedimiento matemático correcto:</strong><p>${a.solution}</p></div>
          <div class="subcard"><strong>Cómo resolver tu duda:</strong><p>Vuelve a hacer el ejercicio escribiendo primero la fórmula general y luego sustituyendo los datos. Compara tu resultado con cada línea del procedimiento anterior hasta ubicar la diferencia.</p></div>
        </div>
      </article>`).join('');
  }
  const logHtml = state.log.length ? state.log.map((e,i)=>`<tr><td>${i+1}</td><td>${e.time.toLocaleString()}</td><td>${escapeHtml(e.text)}</td></tr>`).join('') : '<tr><td colspan="3">Sin eventos registrados.</td></tr>';

  const html = `<!DOCTYPE html><html lang="es"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>Informe final · Laberinto Chino</title>
    <script>window.MathJax={tex:{inlineMath:[['\\\\(','\\\\)']],displayMath:[['\\\\[','\\\\]']],processEscapes:true},svg:{fontCache:'global'},options:{skipHtmlTags:['script','noscript','style','textarea','pre','code']}};<\/script>
    <script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"><\/script>
    <style>
      :root{--blue:#0b3d79;--blue2:#06234c;--gold:#b8860b;--soft:#f7f9fd;--paper:#fffdf7;--rose:#d63b5f;--ok:#0b7f54;--ink:#10243d;--line:#e7edf5;}
      *{box-sizing:border-box} body{margin:0;background:linear-gradient(180deg,#f4f7fb,#fff);color:var(--ink);font-family:Georgia,'Times New Roman',serif;line-height:1.58;font-size:16px}.page{width:min(980px,calc(100% - 28px));margin:22px auto 56px}.hero,.section{background:var(--paper);border:1px solid #e4eaf3;border-radius:24px;padding:26px;margin:22px 0;box-shadow:0 10px 28px rgba(8,35,74,.08)}.hero{border:3px solid rgba(214,59,95,.55);text-align:center}.stamp{background:linear-gradient(180deg,#143e72,#071f43);color:#fff;border-radius:18px;padding:18px;margin-bottom:18px;box-shadow:inset 0 0 0 2px rgba(255,255,255,.18)}.stamp h1{margin:0;font-size:clamp(2.1rem,6vw,4.3rem);letter-spacing:2px;text-transform:uppercase;color:#fff}.stamp h2{margin:10px 0 0;font-size:clamp(1.25rem,3vw,2.2rem);color:#ffe7a3}.eyebrow{letter-spacing:4px;text-transform:uppercase;color:var(--gold);font-weight:900;font-size:.82rem}.title{font-size:clamp(2rem,5vw,4rem);line-height:.98;color:#072e59;margin:10px 0 8px}.subtitle{font-size:1.55rem;color:#956507;font-weight:900;margin:0 0 16px}.cards{display:grid;grid-template-columns:repeat(4,1fr);gap:14px;margin:24px 0}.metric{background:linear-gradient(180deg,#0d4780,#061f43);color:#fff;border-radius:18px;padding:18px;text-align:left;min-height:118px}.metric b{font-size:1.9rem;color:#ffde79}.metric span{display:block;text-transform:uppercase;letter-spacing:.8px;font-size:.76rem;font-weight:900;color:#e9f4ff}.metric.red{background:linear-gradient(180deg,#d63b5f,#a80929)}h2{font-size:2rem;color:#072e59;margin:0 0 14px;border-bottom:3px solid rgba(184,134,11,.35);padding-bottom:8px}.bar-row{background:#f6f9fd;border:1px solid #e1e9f3;border-radius:16px;padding:13px 14px;margin:12px 0}.bar-label{display:flex;justify-content:space-between;gap:12px;color:#12365c}.bar-track{height:14px;background:#e7eef8;border-radius:999px;overflow:hidden;box-shadow:inset 0 1px 2px rgba(0,0,0,.08)}.bar-fill{height:100%;background:linear-gradient(90deg,#0b3d79,#19b8ad,#ffd35a);border-radius:999px}.formula-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:16px}.formula-card,.question-card{border:1px solid #e0e7f0;border-radius:18px;padding:18px;background:#fff;box-shadow:0 5px 18px rgba(8,35,74,.05)}.formula-card h3{color:#0b3d79;margin-top:0}.formula,.latex{background:#f7faff;border:1px solid #e0e9f4;border-radius:14px;padding:13px;margin:10px 0;overflow-x:auto}.security-table,table{width:100%;border-collapse:collapse;background:#fff;border-radius:14px;overflow:hidden}th{background:#0b3d79;color:#fff;text-align:left}td,th{padding:12px;border-bottom:1px solid #e8edf5}.question-top{display:flex;align-items:center;gap:13px;margin-bottom:13px}.question-top h3{margin:0;color:#10243d}.question-top p{margin:3px 0 0;color:#617089;font-size:.95rem}.num{width:42px;height:42px;border-radius:50%;display:grid;place-items:center;background:#0b3d79;color:#fff;font-weight:900;flex:0 0 auto}.pill{margin-left:auto;padding:8px 14px;border-radius:999px;font-weight:900}.pill.ok{background:#e5f7ef;color:#0b7f54}.pill.bad{background:#ffedf1;color:#b31336}.twocol{display:grid;grid-template-columns:1fr 1fr;gap:14px}.answer-box{background:#eef6ff;border:1px solid #dbe9f7;border-radius:14px;padding:14px}.answer-box p{margin:6px 0 0}.feedback-panel{background:#fffaf0;border:1px solid #efe1bf;border-radius:18px;padding:16px;margin-top:14px}.feedback-panel h4{font-size:1.1rem;color:#8a620d;margin:0 0 12px}.subcard{background:#fff;border:1px solid #e8edf2;border-radius:13px;padding:12px;margin:10px 0}.mini-check{padding:10px;border:1px solid #e7edf5;border-radius:12px;margin:8px 0}.mini-check.yes{background:#f0fff7}.mini-check.no{background:#fff2f5}.muted{color:#65748a;font-style:italic}.footer{text-align:right;color:#65748a;margin:28px 0}.book-note{background:#fff9e8;border:1px solid #ead8aa;border-radius:16px;padding:15px;margin:18px 0}mjx-container[jax='SVG']{font-size:108%!important;margin:.35em 0}.question-card mjx-container[jax='SVG'],.formula-card mjx-container[jax='SVG']{font-size:112%!important}@media(max-width:760px){.cards{grid-template-columns:repeat(2,1fr)}.formula-grid,.twocol{grid-template-columns:1fr}.page{width:calc(100% - 14px);margin-top:8px}.hero,.section{padding:16px;border-radius:18px}.metric{min-height:94px}.stamp h1{font-size:2.1rem}body{font-size:15px}mjx-container[jax='SVG']{font-size:100%!important}}@media print{body{background:white}.page{width:100%;margin:0}.hero,.section{break-inside:avoid;box-shadow:none}.question-card{break-inside:avoid}.stamp{print-color-adjust:exact;-webkit-print-color-adjust:exact}}
    </style></head><body><main class="page">
      <section class="hero"><div class="stamp"><h1>Informe final</h1><h2>Nota final: ${state.score.toFixed(1)} / 5.0</h2></div><div class="eyebrow">Laberinto Chino · Sucesiones y series</div><div class="title">Travesía Matemática</div><div class="subtitle">Sucesiones · Series · Convergencia</div><p>Reporte pedagógico con fórmulas renderizadas en LaTeX, retroalimentación por pregunta, diagnóstico de desempeño y plan de mejora.</p><div class="cards"><div class="metric"><b>${correct}/${total}</b><span>Aciertos globales</span></div><div class="metric"><b>${pct}%</b><span>Porcentaje global</span></div><div class="metric ${state.treasuresFound>=TREASURE_TOTAL?'':'red'}"><b>${state.treasuresFound}/${TREASURE_TOTAL}</b><span>Tesoros</span></div><div class="metric"><b>${score50}/50</b><span>Equivalente sugerido</span></div></div><div class="book-note">Inicio: ${state.startedAt ? state.startedAt.toLocaleString() : 'No registrado'} · Fin: ${finished.toLocaleString()} · Duración: ${elapsedMin} min ${elapsedSec} s · Estado: ${resultLabel}</div></section>
      <section class="section"><h2>1. Resumen del jugador</h2><div class="cards"><div class="metric"><b>${state.score.toFixed(1)}</b><span>Nota en escala 0–5.0</span></div><div class="metric"><b>${state.steps}</b><span>Pasos dados</span></div><div class="metric"><b>${incorrect}</b><span>Errores</span></div><div class="metric"><b>${treasurePct}%</b><span>Avance de tesoros</span></div></div></section>
      <section class="section"><h2>2. Gráficas de desempeño</h2><h3>Por tema</h3>${statRows(byTopic)}<h3>Por tipo de pregunta</h3>${statRows(byType)}<h3>Por dificultad</h3>${statRows(byDifficulty)}</section>
      <section class="section"><h2>3. Fórmulas y teoremas que debe revisar el estudiante</h2><div class="formula-grid">${formulaCards()}</div></section>
      <section class="section"><h2>4. Plan de mejora individual</h2>${improvementPlan()}</section>
      <section class="section"><h2>5. Registro de seguridad y expedición</h2>${eventTable()}<h3>Bitácora de eventos</h3><table><tr><th>#</th><th>Hora</th><th>Evento</th></tr>${logHtml}</table></section>
      <section class="section"><h2>6. Detalle de preguntas respondidas</h2><p class="muted">Cada tarjeta conserva la respuesta esperada, la pista disponible, la retroalimentación específica y el procedimiento que debía seguirse.</p>${detailedQuestions()}</section>
      <div class="footer">Informe generado automáticamente por el juego · Página HTML tipo libro</div>
    </main></body></html>`;
  const blob = new Blob([html], {type:'text/html;charset=utf-8'});
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `informe_laberinto_chino_tipo_libro_${Date.now()}.html`;
  a.click();
  URL.revokeObjectURL(a.href);
}
function questionTypeLabel(type){
  return {tf:'V/F', statements:'Afirmaciones I, II y III', integer:'Valor entero', choice:'Selección múltiple'}[type] || 'Pregunta';
}
function kindLabel(kind){
  return {regular:'Pregunta regular', treasure:'Tesoro', obstacle:'Muralla de reto', bonus:'Bono del templo', finalChallenge:'Guardián final'}[kind] || kind;
}


function formatDeviceTime(date=new Date()){
  return `${String(date.getHours()).padStart(2,'0')}:${String(date.getMinutes()).padStart(2,'0')}:${String(date.getSeconds()).padStart(2,'0')}`;
}
function updateDeviceClock(){
  const time = formatDeviceTime();
  if(deviceClockValue) deviceClockValue.textContent = time;
  if(clockHud) clockHud.textContent = time;
  document.querySelectorAll('[data-clock-value]').forEach(el=>{ el.textContent = time; });
}
setInterval(updateDeviceClock, 1000);
updateDeviceClock();

// Seguridad docente
function currentTeacherCode(){
  const d = new Date();
  return `${String(d.getHours()).padStart(2,'0')}${String(d.getMinutes()).padStart(2,'0')}N`;
}
function normalizeTeacherCode(value){
  return String(value || '').toUpperCase().replace(/[^0-9A-Z]/g,'').slice(0,5);
}
function securityGate(){
  let gate = document.getElementById('securityGate');
  if(!gate){
    gate = document.createElement('section');
    gate.id = 'securityGate';
    gate.className = 'security-gate hidden';
    gate.innerHTML = `<div class="security-card parchment">
      <div class="seal small-seal">🐉</div>
      <h2>Muralla bloqueada</h2>
      <p id="securityReason">Se detectó un evento no permitido.</p>
      <div class="security-clock-inline"><span>Hora del dispositivo</span><strong data-clock-value>--:--:--</strong></div>
      <div class="security-counter" id="securityCounter">Bloqueo 0/${MAX_SECURITY_LOCKS}</div>
      <p class="teacher-only">Solo el docente puede reanudar la partida.</p>
      <label class="teacher-code-label">Clave docente
        <input id="teacherCodeInput" type="password" inputmode="text" autocomplete="off" placeholder="*****" maxlength="5" aria-label="Clave docente" />
      </label>
      <div id="teacherCodeError" class="teacher-code-error hidden">Clave incorrecta.</div>
      <button id="teacherUnlockBtn" class="primary">Desbloquear partida</button>
    </div>`;
    document.body.appendChild(gate);
    updateDeviceClock();
    const input = gate.querySelector('#teacherCodeInput');
    gate.querySelector('#teacherUnlockBtn').addEventListener('click', async()=>{
      const given = normalizeTeacherCode(input.value);
      if(given === currentTeacherCode()){
        gate.querySelector('#teacherCodeError').classList.add('hidden');
        input.value = '';
        await enterFullscreen();
        securityLockActive = false;
        gate.classList.add('hidden');
        if(gameRunning && questionModal.classList.contains('hidden') && endModal.classList.contains('hidden') && howModal.classList.contains('hidden')) modalOpen=false;
        addEvent('El docente desbloqueó la partida con clave temporal.', 'good');
        resizeCanvas();
      }else{
        if(state.security) state.security.wrongTeacherCodes = (state.security.wrongTeacherCodes || 0) + 1;
        gate.querySelector('#teacherCodeError').classList.remove('hidden');
        input.value = '';
        input.focus();
      }
    });
    input.addEventListener('keydown', e=>{
      if(e.key === 'Enter'){
        e.preventDefault();
        gate.querySelector('#teacherUnlockBtn').click();
      }
    });
  }
  return gate;
}
function triggerSecurityLock(reason, counterKey){
  if(!gameRunning || state.finishedAt) return;
  const now = performance.now();
  if(securityLockActive || now - lastSecurityEventAt < 700) return;
  lastSecurityEventAt = now;
  keys.clear();
  if(state.security && counterKey) state.security[counterKey] = (state.security[counterKey] || 0) + 1;
  if(state.security) state.security.locks = (state.security.locks || 0) + 1;
  const locks = state.security?.locks || 0;
  addEvent(`Bloqueo de seguridad ${locks}/${MAX_SECURITY_LOCKS}: ${reason}.`, 'bad');
  if(locks >= MAX_SECURITY_LOCKS){
    state.cancelled = true;
    finishGame(`Quiz anulado: se alcanzaron ${MAX_SECURITY_LOCKS}/${MAX_SECURITY_LOCKS} bloqueos de seguridad.`);
    return;
  }
  securityLockActive = true;
  modalOpen = true;
  const gate = securityGate();
  gate.querySelector('#securityReason').textContent = reason;
  gate.querySelector('#securityCounter').textContent = `Bloqueo ${locks}/${MAX_SECURITY_LOCKS}`;
  gate.querySelector('#teacherCodeError').classList.add('hidden');
  updateDeviceClock();
  gate.classList.remove('hidden');
  setTimeout(()=>gate.querySelector('#teacherCodeInput')?.focus(), 80);
}
function blockedShortcut(e){
  const k = String(e.key || '').toLowerCase();
  return (e.ctrlKey && ['p','s','u'].includes(k)) ||
    (e.ctrlKey && e.shiftKey && ['i','j','c'].includes(k)) ||
    k === 'f12';
}

// Eventos UI
function isFullscreen(){ return Boolean(document.fullscreenElement || document.webkitFullscreenElement); }
async function enterFullscreen(){
  const el = document.documentElement;
  try{
    if(!isFullscreen()){
      if(el.requestFullscreen) await el.requestFullscreen();
      else if(el.webkitRequestFullscreen) await el.webkitRequestFullscreen();
    }
  }catch(err){
    console.warn('No se pudo activar pantalla completa:', err);
  }
}
function exitFullscreenIfNeeded(){
  try{
    if(document.fullscreenElement && document.exitFullscreen) document.exitFullscreen();
  }catch(err){}
}
function fullscreenGate(){
  let gate = document.getElementById('fullscreenGate');
  if(!gate){
    gate = document.createElement('section');
    gate.id = 'fullscreenGate';
    gate.className = 'fullscreen-gate hidden';
    gate.innerHTML = `<div class="fullscreen-card parchment"><div class="seal small-seal">🐉</div><h2>Pantalla completa requerida</h2><div class="security-clock-inline"><span>Hora del dispositivo</span><strong data-clock-value>--:--:--</strong></div><p>La travesía debe permanecer en pantalla completa.</p><button id="restoreFullscreenBtn" class="primary">Reingresar en pantalla completa</button></div>`;
    document.body.appendChild(gate);
    updateDeviceClock();
    gate.querySelector('#restoreFullscreenBtn').addEventListener('click', async()=>{
      await enterFullscreen();
      if(isFullscreen()){
        gate.classList.add('hidden');
        if(gameRunning && questionModal.classList.contains('hidden') && endModal.classList.contains('hidden') && howModal.classList.contains('hidden')) modalOpen=false;
        resizeCanvas();
      }
    });
  }
  return gate;
}
function enforceFullscreen(){
  const gate = fullscreenGate();
  if(gameRunning && !isFullscreen()){
    gate.classList.add('hidden');
    triggerSecurityLock('Salida de pantalla completa o intento de abandonar el modo de evaluación', 'fullscreenExits');
  }else if(!securityLockActive){
    gate.classList.add('hidden');
  }
}
document.addEventListener('fullscreenchange',()=>{ enforceFullscreen(); resizeCanvas(); });
document.addEventListener('webkitfullscreenchange',()=>{ enforceFullscreen(); resizeCanvas(); });
document.addEventListener('visibilitychange',()=>{ if(gameRunning && document.hidden) triggerSecurityLock('Pestaña oculta, minimización o intento de cambiar de pantalla', 'hiddenTabs'); if(!document.hidden) enforceFullscreen(); });

Array.from(document.querySelectorAll('.animal-choice')).forEach(btn=>{
  btn.addEventListener('click',()=>{document.querySelectorAll('.animal-choice').forEach(b=>b.classList.remove('selected'));btn.classList.add('selected');selectedAnimal=btn.dataset.animal;});
});

async function startGameFromButton(event){
  if(event){ event.preventDefault(); event.stopPropagation(); }
  const btn = document.getElementById('startBtn');
  if(btn){ btn.disabled = true; btn.textContent = 'Abriendo la muralla...'; }

  // Se intenta solicitar pantalla completa de inmediato porque Chrome exige
  // que esta acción esté asociada directamente al clic del usuario. Si el
  // navegador la demora o la rechaza, la partida igualmente se crea y luego
  // se muestra el bloqueo docente de pantalla completa.
  try{ await enterFullscreen(); }catch(err){ console.warn('Pantalla completa pendiente:', err); }

  try{
    resetGame();
    showScreen('game');
    resizeCanvas();
    updateHUD();
    setTimeout(()=>{ resizeCanvas(); enforceFullscreen(); }, 180);
  }catch(err){
    console.error('Error real al iniciar el laberinto:', err);
    alert('No se pudo iniciar el laberinto por un error interno ya registrado en consola. Descarga la versión corregida o abre nuevamente index.html en Chrome.');
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = 'Entrar a la muralla'; }
  }
}
window.startGameFromButton = startGameFromButton;
document.getElementById('startBtn').addEventListener('click', startGameFromButton);

document.getElementById('howBtn').addEventListener('click',()=>howModal.classList.remove('hidden'));
document.getElementById('howGameBtn').addEventListener('click',()=>{modalOpen=true;howModal.classList.remove('hidden');});
document.getElementById('closeHowBtn').addEventListener('click',()=>{howModal.classList.add('hidden'); if(screens.game.classList.contains('active') && questionModal.classList.contains('hidden') && endModal.classList.contains('hidden') && !securityLockActive) modalOpen=false;});
document.getElementById('finishBtn').addEventListener('click',()=>finishGame('Partida finalizada manualmente.'));
document.getElementById('mainMenuBtn').addEventListener('click',()=>{if(confirm('¿Volver al menú principal? Se finalizará la partida actual.')){gameRunning=false;modalOpen=false;fullscreenGate().classList.add('hidden');showScreen('menu');}});
hintBtn.addEventListener('click',()=>{hintText.classList.toggle('hidden'); typesetMath();});
submitAnswerBtn.addEventListener('click',submitAnswer);
continueBtn.addEventListener('click',continueAfterQuestion);
document.getElementById('downloadReportBtn').addEventListener('click',generateReport);
document.getElementById('restartBtn').addEventListener('click',()=>{endModal.classList.add('hidden');modalOpen=false;gameRunning=false;fullscreenGate().classList.add('hidden');showScreen('menu');});

window.addEventListener('keydown',e=>{
  if(e.key === 'Escape' && gameRunning){
    e.preventDefault();
    triggerSecurityLock('Uso de la tecla Escape', 'escapeKey');
    return;
  }
  if(e.key === 'PrintScreen' && gameRunning){
    e.preventDefault();
    triggerSecurityLock('Intento de pantallazo detectado por el navegador', 'printScreen');
    return;
  }
  if(blockedShortcut(e) && gameRunning){
    e.preventDefault();
    triggerSecurityLock('Atajo del navegador no permitido durante el juego', 'blockedShortcuts');
    return;
  }
  if(keyToDir[e.key]){ e.preventDefault(); keys.add(e.key); }
  if(e.key==='Enter' && !questionModal.classList.contains('hidden') && !submitAnswerBtn.classList.contains('hidden')) submitAnswer();
});
window.addEventListener('keyup',e=>{
  if(e.key === 'PrintScreen' && gameRunning){
    e.preventDefault();
    triggerSecurityLock('Intento de pantallazo detectado por el navegador', 'printScreen');
    return;
  }
  if(keyToDir[e.key]){ e.preventDefault(); keys.delete(e.key); }
});
window.addEventListener('blur',()=>{ if(gameRunning) triggerSecurityLock('Cambio de ventana o pérdida de foco', 'focusLosses'); keys.clear(); });
window.addEventListener('contextmenu',e=>{ if(gameRunning){ e.preventDefault(); triggerSecurityLock('Clic derecho o menú contextual no permitido', 'rightClicks'); } });

// Polyfill roundRect si el navegador es antiguo
if(typeof CanvasRenderingContext2D !== 'undefined' && !CanvasRenderingContext2D.prototype.roundRect){
  CanvasRenderingContext2D.prototype.roundRect = function(x,y,w,h,r){
    r=Math.min(r,w/2,h/2);this.beginPath();this.moveTo(x+r,y);this.arcTo(x+w,y,x+w,y+h,r);this.arcTo(x+w,y+h,x,y+h,r);this.arcTo(x,y+h,x,y,r);this.arcTo(x,y,x+w,y,r);this.closePath();return this;
  };
}
resizeCanvas();
