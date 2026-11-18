# The lifted torus and Conrad's relation (4.3.1)

Worker 65. Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1, proof pp. 129-130). Throughout, `X : Ext S` is the point-level data
from `Setup`.

## Commutativity hypothesis

- `Loc.exists_sqrt`: fppf-locally every unit is a square.
- `X.DComm` is the proposition `comm (h s) (h t) = 1` for all units `s`, `t` over every test
  object. It says that lifts of diagonal matrices commute: this is the commutativity of
  Conrad's `D′`. `commute_h` turns it into `Commute e e'` for lifts `e` of `h s` and `e'` of
  `h t`. This module does not prove `DComm`. Results that need it take `hD : X.DComm` as a
  hypothesis. It is proved in `DComm` for extensions by separated commutative group schemes.

## The lifts

- `xl u = rootLift false u` and `yl v = rootLift true v` are Conrad's `x′(u)` and `y′(v)`, the
  homomorphic lifts from `Splitting`, with `Q_xl`, `Q_yl`, naturality (`xl_res`, `yl_res`),
  additivity (`xl_add`, `yl_add`, `xl_zero`, `yl_zero`, `xl_neg`, `yl_neg`) and conjugation by
  lifts of `h(s)` (`xl_conj`: `u ↦ s² u`; `yl_conj`: `v ↦ s⁻² v`).
- `gl t = y′(-1/t) x′(t) y′(-1/t)` and `hl t = gl t · (gl 1)⁻¹` are Conrad's `g′(t)` and `h′(t)`,
  lifting `w(t)` and `h(t)` (`Q_gl`, `Q_hl`). They are natural (`gl_res`, `hl_res`), and
  `hl 1 = 1`. Conjugation by a lift of `h(s)` sends `gl t` to `gl (s² t)` (`gl_conj`), hence
  `hl t` to `gl (s² t) · gl (s²)⁻¹` (`hl_conj`).
- `hl_xl`, `hl_yl`, `xl_hl`, `yl_hl`: `h′(s) x′(u) = x′(s² u) h′(s)`,
  `h′(s) y′(v) = y′(s⁻² v) h′(s)` and the corresponding identities with `h′(s)` on the right.

## Results under `DComm`

- `hl_sq_mul`: `h′(s² t) = h′(t) h′(s²)`, from `hl_conj` and commutativity of `h′(s)` with `h′(t)`.
- `hl_mul`, `hl_inv`: `h′` is a homomorphism. Fppf-locally `a = r²` (`Loc.exists_sqrt`), and
  `hl_sq_mul` with commutativity gives `h′(ab) = h′(a) h′(b)`. The equality descends by
  `Loc.ext`.
- `gl_mul_left`: `g′(st) = h′(s) g′(t)`.
- `xl_yl_of_unit`: if `u` is a unit and `s = 1 + uv` is a unit, then
  `x′(u) y′(v) = y′(v/s) h′(s) x′(u/s)`. With `t = u/s`, write
  `x′(u) = y′(1/u) g′(u) y′(1/u)` and `g′(u) = h′(s) g′(t)`, then move `h′(s)` past `y′` with
  `hl_yl`. This is the computation in Conrad's proof.
- `xl_yl_of_split`: the same relation when `u = u′ + u″` with `u′`, `u″` and `1 + u″v` units.
  It applies `xl_yl_of_unit` twice and uses `hl_mul`.
- `xl_yl` (Conrad's relation (4.3.1)): `x′(u) y′(v) = y′(v/s) h′(s) x′(u/s)` whenever
  `s = 1 + uv` is a unit, for arbitrary `u`. The polynomial `X (u - X) (1 + vX)` is nowhere
  degenerate, so fppf-locally it takes a unit value `r`. With `u′ = u - r` and `u″ = r`,
  `xl_yl_of_split` applies, and the equality descends by `Loc.ext`.
