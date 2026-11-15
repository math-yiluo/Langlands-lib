# Decay of principal-series vectors along the rank-one chart

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetDecay`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source. It imports
`ComplexSwapJacquetChart` (for `chart`).

Throughout, `ds = pre ++ d :: e :: post` is a list of complex character data, `i : Fin n` is
the position of `d` (`hi : (i : ℕ) = pre.length`) and `j` the position of `e`
(`hj : (j : ℕ) = i + 1`). The functions `h` lie in `complexStandardModule n ds`, the smooth
principal series of `ds`. The main results bound `h(s x(z))`, where `s x(z) = chart i j hj z`,
assuming `hre : 0 ≤ Re(t_d - t_e)` (exponents `t_d = d.exponent`, `t_e = e.exponent`).

## Smoothness along curves

* `contDiff_apply_of_val`: if `h` is smooth on `GL_n(ℂ)` (`ContMDiff` for `matrixModel ℂ n`)
  and `T : ℂ → GL_n(ℂ)` has smooth underlying matrices, then `w ↦ h(T w)` is real-smooth.
  Proof: write `h ∘ T = unitsExtension h ∘ (val ∘ T)` and use `contDiffOn_unitsExtension`.
* `contDiff_transvection`: `w ↦ Matrix.transvection a b w = 1 + w E_ab` is smooth.
* `contDiff_apply_chart`: `z ↦ h(s x(z))` is smooth.
* `lowerChart i j hj w = 1 + w E_ji` (a lower unipotent transvection), with
  `lowerChart_zero : lowerChart i j hj 0 = 1` and `contDiff_apply_lowerChart`:
  `w ↦ h(1 + w E_ji)` is smooth.

## The factorization of the chart

* `chartTorus i j z` for `z : ℂˣ`: the diagonal entries `-z⁻¹` at `i`, `z` at `j`, `1`
  elsewhere.
* `chartUnipotent i j hj z`: the transvection `1 - z E_ij` as an element of `upperUnipotent n ℂ`.
  Its strict lower part vanishes and its diagonal is `1`.
* `chart_eq_mul` (for `z ≠ 0`):
  `s x(z) = diag(chartTorus z) · (1 - z E_ij) · (1 + z⁻¹ E_ji)`.
  Proof: compare entries of the underlying matrices. Only the `2 × 2` block in rows and columns
  `i, j` is nontrivial: `[[0, 1], [1, z]] = [[-1/z, 0], [0, z]] · [[1, -z], [0, 1]] ·
  [[1, 0], [1/z, 1]]`.
* `apply_chart_eq`: for `h` in `principalSeries ℂ n χ` and `z ≠ 0`,
  `h(s x(z)) = principalSeriesCharacter ℂ n χ (chartTorus z) · h(1 + z⁻¹ E_ji)`. This is the
  left transformation law of the principal series applied to the factorization.

## The absolute value of the character

* `norm_character`: `‖d.character w‖ = ‖w‖^(2 Re t_d)`.
* `complexPositionCharacter_one`, `complexPositionCharacter_append_length`,
  `complexPositionCharacter_append_length_succ`: the position characters of a list are `1` at
  `1`, and those of `pre ++ d :: e :: post` at positions `|pre|` and `|pre| + 1` are the
  characters of `d` and `e`.
* `norm_principalSeriesCharacter_chartTorus`: the character of the standard module of `ds` at
  `chartTorus z` has absolute value `‖z‖^(-2 - 2 Re(t_d - t_e))`. Proof: only the factors at
  `i` and `j` differ from `1` (`Fintype.prod_eq_mul`). Each is the character of `d` resp. `e`
  times the modulus factor. Taking logarithms reduces the claim to a linear identity in
  `log ‖z‖`, which uses `j = i + 1`.
* `norm_principalSeriesCharacter_chartTorus_le`: for `‖z‖ ≥ 1` and `hre`, this is at most
  `(‖z‖^2)⁻¹`.

## Decay along the chart

* `exists_bound_ball`, `exists_lipschitz_ball`: a continuous `ψ : ℂ → ℂ` is bounded on the
  closed unit ball. A `C¹` one satisfies `‖ψ w - ψ 0‖ ≤ L ‖w‖` there (mean value inequality,
  `Convex.norm_image_sub_le_of_norm_fderiv_le`).
* `inv_sq_le_two_mul_inv`, `inv_cube_le_eight_mul_inv`, `one_le_two_mul_inv`,
  `one_le_eight_mul_inv_cube`: the real inequalities `r⁻² ≤ 2 (1 + r)⁻¹` and
  `r⁻³ ≤ 8 (1 + r)⁻³` for `r ≥ 1`, and `1 ≤ 2 (1 + r)⁻¹` and `1 ≤ 8 (1 + r)⁻³` for
  `0 ≤ r ≤ 1`.
* `norm_apply_chart_le`: for `‖z‖ ≥ 1`, `‖h(s x(z))‖ ≤ ‖z‖⁻² ‖h(1 + z⁻¹ E_ji)‖`.
* `exists_bound_chart`: there is `C` with `‖h(s x(z))‖ ≤ C (1 + ‖z‖)⁻¹` for all `z`. Proof:
  for `‖z‖ ≤ 1` bound `h(s x(z))` by its maximum on the unit ball. For `‖z‖ ≥ 1` use
  `norm_apply_chart_le` and the bound of `w ↦ h(1 + w E_ji)` on the unit ball.
* `exists_bound_chart_of_eq_zero`: if moreover `h(1) = 0`, there is `C` with
  `‖h(s x(z))‖ ≤ C ((1 + ‖z‖)^3)⁻¹`. Proof: as before, except that for `‖z‖ ≥ 1` the Lipschitz
  bound gives `‖h(1 + z⁻¹ E_ji)‖ = ‖h(1 + z⁻¹ E_ji) - h(1)‖ ≤ L ‖z‖⁻¹`, hence
  `‖h(s x(z))‖ ≤ L ‖z‖⁻³`.
