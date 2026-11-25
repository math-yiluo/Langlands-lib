# Elementary matrices in `SL₂` over a commutative ring

Internal supporting development for the proof of
`Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement` (Conrad, *Reductive group
schemes*, Proposition 4.3.1, proof on pp. 126-131). It records the matrix identities used in
Conrad's proof. They are elementary computations over an arbitrary commutative ring `R`, all in
the namespace `Langlands.GroupScheme.SL2CentralExtension.Mat`.

## Points

- `SL2 R` is `Matrix.SpecialLinearGroup (Fin 2) R`. `ext'` checks equality on the four entries.
  The simp lemmas `mul_00`, …, `inv_00`, …, `one_00`, … give the entries of products, inverses and
  `1`.
  `det_eq` is `g₀₀ g₁₁ - g₀₁ g₁₀ = 1`.
- Conrad's points: `x u = [[1, u], [0, 1]]`, `y v = [[1, 0], [v, 1]]` and
  `h t = diag(t, t⁻¹)` for a unit `t`.
- `w t = y(-1/t) x(t) y(-1/t)`, which is `[[0, t], [-1/t, 0]]` by `w_00`, `w_01`, `w_10` and
  `w_11`. This is Conrad's `g(t)`, and `w_mul_w_one_inv` gives `w(t) w(1)⁻¹ = h(t)`.

## Identities

- `x_add`, `y_add`, `x_neg`, `y_neg`: `x` and `y` are homomorphisms from the additive group.
  `h_mul`, `h_inv`, `h_one` and `h_comm` say that `h` is a homomorphism from the units with
  commuting values.
- `h_x`: `h(t) x(u) = x(t² u) h(t)`. `h_y`: `h(t) y(v) = y(t⁻² v) h(t)`.
- Uniform notation for the two root groups: `root false = x`, `root true = y`, `lam false s =
  h(s)`, `lam true s = h(s⁻¹)`. Then `lam_root`, `lam_root_conj`: `lam b s` conjugates
  `root b u` to `root b (s² u)`. `lam_root_commutator`: the commutator
  `[lam b s, root b u]` equals `root b ((s² - 1) u)`. This is Conrad's identity
  `h(t) x(u) h(t)⁻¹ x(u)⁻¹ = x((t² - 1) u)` and its analogue for `y`. Also `root_add`,
  `root_zero`, `root_neg`, `root_comm`, `lam_mul`, `lam_comm` and `lam_eq_h`.
- `map_x`, `map_y`, `map_h`, `map_root`, `map_lam`, `map_w`, `map_yhx`: all these points are
  compatible with `Matrix.SpecialLinearGroup.map f` for a ring map `f`. On units, `f` acts
  through `Units.map f.toMonoidHom`.

## The open cell

- `cell g` means that `g₀₀` is a unit. `yhx a t b = y(a) h(t) x(b)` lies in the cell
  (`cell_yhx`). Its entries are given by `yhx_00`, `yhx_01` and `yhx_10`. The decomposition is
  unique (`yhx_injective`). Every cell point with `t = g₀₀` equals
  `yhx (g₁₀/g₀₀) t (g₀₁/g₀₀)` (`eq_yhx`).
- `x_mul_y`: if `s = 1 + uv` is a unit, then `x(u) y(v) = y(v/s) h(s) x(u/s)`. This is the
  relation used in Conrad's proof for the multiplication on the open cell.
- `x_mul_00`: `(x(r) g)₀₀ = g₀₀ + r g₁₀`. `col_unimodular` and `inv_col_unimodular`: the
  pairs `(g₀₀, g₁₀)` and `(g₁₁, -g₁₀)` generate the unit ideal. These are used to move a
  matrix into the open cell fppf-locally by left multiplication with some `x(r)`.
