# Integration by parts on `ℂ` for the rank-one Jacquet functional

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetAnalysis`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source. It imports only Mathlib.

All integrals are over `ℂ` with Lebesgue measure `volume`. `φ : ℂ → ℂ` is real `C¹`
(`ContDiff ℝ 1 φ`), and `Dφ(z) = fderiv ℝ φ z : ℂ →L[ℝ] ℂ`. These are the four integral
identities the rank-one Jacquet functional needs (`ComplexSwapJacquetFunctional`).

## The majorant `(1 + |z|)⁻³`

* `integrable_inv_one_add_norm_pow_three`: `z ↦ ((1 + ‖z‖)^3)⁻¹` is integrable on `ℂ`. Proof:
  Mathlib's `integrable_one_add_norm` with exponent `3 > 2 = dim_ℝ ℂ`.
* `nonneg_of_bound`: a bound `‖φ z‖ ≤ C ((1 + ‖z‖)^3)⁻¹` for all `z` forces `0 ≤ C` (take
  `z = 0`).
* `integrable_of_bound`: a continuous `φ` with that bound is integrable (domination).
* `tendsto_cobounded_of_bound`: a bound `‖φ z‖ ≤ C (1 + ‖z‖)⁻¹` gives `φ → 0` along
  `Bornology.cobounded ℂ`.
* `tendsto_line_re_atTop/atBot`, `tendsto_line_im_atTop/atBot`, `hasDerivAt_line_re`,
  `hasDerivAt_line_im`: the horizontal line `x ↦ x + i y` and the vertical line
  `y ↦ x + i y` tend to infinity in `ℂ`, with derivatives `1` and `i`.

## The four identities

* `integral_fderiv_one_eq_zero`: if `z ↦ Dφ(z) 1` is integrable and `φ → 0` at infinity, then
  `∫ Dφ(z) 1 dz = 0`. Proof: transport the integral to `ℝ × ℝ` by
  `Complex.volume_preserving_equiv_real_prod` and apply Fubini (`integral_prod_symm`). For
  almost every `y`, `x ↦ Dφ(x + i y) 1` is integrable and is the derivative of
  `x ↦ φ(x + i y)`. That function tends to `0` at `±∞`, so its integral is `0` by
  `integral_of_hasDerivAt_of_tendsto`.
* `integral_fderiv_I_eq_zero`: the same for the direction `i`, `∫ Dφ(z) i dz = 0`. Here
  Fubini is applied in the other order and the vertical lines are used.
* `integral_fderiv_apply_self` (Euler's identity): if `‖φ z‖` and `‖Dφ(z) z‖` are both bounded
  by `C ((1 + ‖z‖)^3)⁻¹`, then `∫ Dφ(z) z dz = -2 ∫ φ`. Proof: for real `r` near `1`,
  `F(r) = ∫ φ(r z) dz` equals `r⁻² ∫ φ` (`Measure.integral_comp_smul_of_nonneg`,
  `dim_ℝ ℂ = 2`). Differentiation under the integral sign
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the ball `|r - 1| < 1/2`) gives
  `F'(1) = ∫ Dφ(z) z`. The domination uses
  `Dφ(r z) z = r⁻¹ Dφ(r z)(r z)` and `inv_one_add_mul_pow_three_le`:
  `((1 + r x)^3)⁻¹ ≤ 8 ((1 + x)^3)⁻¹` for `r ≥ 1/2`, `x ≥ 0`. The derivative of `r⁻² ∫ φ` at
  `1` is `-2 ∫ φ`; uniqueness of derivatives finishes the proof.
* `integral_fderiv_apply_I_mul_self`: if `‖φ z‖` and `‖Dφ(z)(i z)‖` are both bounded by
  `C ((1 + ‖z‖)^3)⁻¹`, then `∫ Dφ(z)(i z) dz = 0`. Proof: `G(θ) = ∫ φ(e^{iθ} z) dz` is
  constant, since the rotation `z ↦ e^{iθ} z` is a measure-preserving linear isometry
  (`rotation`, `LinearIsometryEquiv.measurePreserving`). Differentiation under the integral
  sign at `θ = 0` (domination by the rotation-invariant bound) gives
  `G'(0) = ∫ Dφ(z)(i z) = 0`.
