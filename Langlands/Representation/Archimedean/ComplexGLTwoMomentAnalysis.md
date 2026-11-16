# Weighted integration by parts on `ℂ`

Module `Langlands.Representation.Archimedean.ComplexGLTwoMomentAnalysis`, namespace
`Langlands.Archimedean.ComplexGLTwoMoment`. This is an internal helper module for the proof of
`ComplexGLTwoMomentJacquetStatement` (`ComplexGLTwoMomentJacquetProof`), and has no literature
source. It imports `ComplexSwapJacquetAnalysis`, whose unweighted identities
`integral_fderiv_one_eq_zero` and `integral_fderiv_I_eq_zero` (`∫ Dψ(z) 1 = ∫ Dψ(z) i = 0`
for `ψ → 0` at infinity with integrable derivative) it reuses.

All integrals are over `ℂ` with Lebesgue measure `volume`. `φ : ℂ → ℂ` is real `C¹`
(`ContDiff ℝ 1 φ`) and `Dφ(z) = fderiv ℝ φ z : ℂ →L[ℝ] ℂ`. The weight is
`p(z) = weight i j z = z^i z̄^j`. The majorant is `(1 + |z|)^(-r)` (a real power), which is
integrable for `r > 2 = dim_ℝ ℂ`. The `ComplexSwapJacquet` versions of these lemmas
use the fixed majorant `(1 + |z|)⁻³`. That is too weak here, because the weight raises the
exponent by `i + j`.

## The majorant `(1 + |z|)^(-r)`

* `integrable_one_add_norm_rpow`: `(1 + |z|)^(-r)` is integrable for `2 < r` (Mathlib's
  `integrable_one_add_norm`).
* `nonneg_of_bound_rpow`: a bound `‖φ z‖ ≤ C (1 + |z|)^(-r)` for all `z` forces `0 ≤ C`
  (take `z = 0`).
* `integrable_of_bound_rpow`: an a.e.-strongly measurable `φ` with such a bound and `2 < r`
  is integrable (domination).
* `tendsto_cobounded_of_bound_rpow`: such a bound with `0 < r` gives `φ → 0` along
  `Bornology.cobounded ℂ` (squeeze with `(1 + |z|)^(-r) → 0`).
* `one_add_mul_rpow_neg_le`: `(1 + ρ x)^(-r) ≤ 2^r (1 + x)^(-r)` for `ρ ≥ 1/2`, `x ≥ 0`,
  `r ≥ 0`. This is the domination used for dilations.

## Euler's identity and rotation invariance

* `integral_fderiv_apply_self_rpow`: if `2 < r` and `‖φ z‖`, `‖Dφ(z) z‖` are both bounded by
  `C (1 + |z|)^(-r)`, then `∫ Dφ(z) z = -2 ∫ φ`. Proof: for `ρ` near `1`,
  `F(ρ) = ∫ φ(ρ z) dz = ρ⁻² ∫ φ` (`Measure.integral_comp_smul_of_nonneg`, `dim_ℝ ℂ = 2`).
  Differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  on the ball `|ρ - 1| < 1/2`) gives `F'(1) = ∫ Dφ(z) z`. The domination comes from
  `Dφ(ρ z) z = ρ⁻¹ Dφ(ρ z)(ρ z)` and `one_add_mul_rpow_neg_le`, with bound
  `2 · 2^r · C (1 + |z|)^(-r)`. The derivative of `ρ⁻² ∫ φ` at `1` is `-2 ∫ φ`, and
  uniqueness of derivatives finishes the proof.
* `integral_fderiv_apply_I_mul_self_rpow`: if `2 < r` and `‖φ z‖`, `‖Dφ(z)(i z)‖` are both
  bounded by `C (1 + |z|)^(-r)`, then `∫ Dφ(z)(i z) = 0`. Proof: `G(θ) = ∫ φ(e^{iθ} z) dz` is
  constant, because the rotation by `Circle.exp θ` preserves the measure
  (`LinearIsometryEquiv.measurePreserving`). Differentiation under the integral sign at `θ = 0`
  gives `G'(0) = ∫ Dφ(z)(i z)`. The domination uses the rotation-invariant bound.

## The weight `z^i z̄^j`

* `weight i j z = z^i z̄^j`, and `weightDeriv i j z v = i z^(i-1) v z̄^j + j z^i z̄^(j-1) v̄`.
* `contDiff_weight`: the weight is smooth over `ℝ`. `hasFDerivAt_weight` and
  `fderiv_weight_apply` show that its real derivative at `z` sends `v` to `weightDeriv i j z v`
  (product rule for `z ↦ z^i` and `z ↦ (conj z)^j`).
* `norm_weight`: `|p(z)| = |z|^(i+j)`.
* `weightDeriv_self`: `Dp(z)(z) = (i + j) p(z)`. `weightDeriv_I_mul_self`:
  `Dp(z)(i z) = i (i - j) p(z)`. Both use `natCast_mul_pow_sub_one_mul`:
  `i z^(i-1) z = i z^i`, which also holds for `i = 0`.
* `norm_weightDeriv_le`: `|Dp(z)(v)| ≤ (i + j) |v| (1 + |z|)^(i+j)`. The lemmas
  `norm_weightDeriv_const_le` (`|v| = 1`), `norm_weightDeriv_self_le` (`v = z`) and
  `norm_weightDeriv_I_mul_self_le` (`v = i z`) bound it by `(i + j) (1 + |z|)^(i+j)`.

## Bounds for products with the weight

* `mul_le_rpow_aux`: from `x ≤ C u^(-a)` and `y ≤ K u^m` (with `0 < u` and `x, y ≥ 0`),
  `x y ≤ C K u^(-(a - m))`.
* `norm_weight_le`: `|z^i z̄^j| ≤ (1 + |z|)^m` for `i + j ≤ m`.
* `norm_mul_weight_le`: if `‖φ z‖ ≤ C (1 + |z|)^(-a)` for all `z` and `i + j ≤ m`, then
  `‖φ(z) p(z)‖ ≤ C (1 + |z|)^(-(a - m))`.
* `fderiv_mul_weight_apply`: the product rule `D(φ p)(z)(v) = Dφ(z)(v) p(z) + φ(z) Dp(z)(v)`.
* `contDiff_mul_weight`: `φ p` is `C¹` when `φ` is.
* `norm_fderiv_mul_weight_le`: if `φ` and `Dφ(z)(w(z))` are bounded by `C (1 + |z|)^(-a)` and
  `|Dp(z)(w(z))| ≤ (i + j)(1 + |z|)^(i+j)`, then
  `|D(φ p)(z)(w(z))| ≤ C (1 + (i + j)) (1 + |z|)^(-(a - (i + j)))`.

## Weighted integration by parts

In this section `i + j + 2 < a` (`ha`). `φ` is bounded by `C (1 + |z|)^(-a)` (`hb`), and the
derivatives named in each lemma have the same bound with the same constant `C`.

* `integrable_mul_weight`: for continuous `φ`, `φ(z) z^{i'} z̄^{j'}` is integrable whenever
  `i' + j' ≤ i + j` (the majorant exponent is `a - (i + j) > 2`).
* `integrable_fderiv_apply_mul_weight`: if `w` is continuous and `Dφ(z)(w(z))` is bounded by
  `C (1 + |z|)^(-a)`, then `Dφ(z)(w(z)) p(z)` is integrable.
* `integral_fderiv_const_mul_weight_aux`: for a constant direction `w` with
  `∫ D(φ p)(z)(w) = 0`, the product rule and `Dp(z)(w) = i w z^(i-1) z̄^j + j w̄ z^i z̄^(j-1)` give
  `∫ Dφ(z)(w) p = -(i w ∫ φ z^(i-1) z̄^j) - j w̄ ∫ φ z^i z̄^(j-1)`.
* `integral_fderiv_mul_weight` (**translation**): if `Dφ(z) 1` and `Dφ(z) i` are bounded, then
  for every `c ∈ ℂ`,
  `∫ Dφ(z)(c) z^i z̄^j = -(i c ∫ φ z^(i-1) z̄^j + j c̄ ∫ φ z^i z̄^(j-1))`.
  Proof: `ψ = φ p` tends to `0` at infinity, and `Dψ(z) 1`, `Dψ(z) i` are integrable by
  `norm_fderiv_mul_weight_le`. So `ComplexSwapJacquet.integral_fderiv_one_eq_zero` and
  `integral_fderiv_I_eq_zero` give `∫ Dψ(z) 1 = ∫ Dψ(z) i = 0`, and the auxiliary lemma
  applies with `w = 1` and `w = i`. A general `c` is handled by real-linearity:
  `Dφ(z)(c) = Re c · Dφ(z) 1 + Im c · Dφ(z) i`, with `c = Re c + Im c · i` and
  `c̄ = Re c - Im c · i`.
* `integral_fderiv_self_mul_weight` (**Euler**): if `Dφ(z) z` is bounded, then
  `∫ Dφ(z)(z) z^i z̄^j = -(2 + i + j) ∫ φ z^i z̄^j`. Proof: Euler's identity
  `integral_fderiv_apply_self_rpow` for `ψ = φ p` with exponent `a - (i + j) > 2` and constant
  `C (1 + (i + j))`, together with `Dψ(z)(z) = Dφ(z)(z) p(z) + (i + j) φ(z) p(z)`
  (`weightDeriv_self`).
* `integral_fderiv_I_mul_self_mul_weight` (**rotation**): if `Dφ(z)(i z)` is bounded, then
  `∫ Dφ(z)(i z) z^i z̄^j = -i (i - j) ∫ φ z^i z̄^j`. Proof: the same argument with
  `integral_fderiv_apply_I_mul_self_rpow` and `Dψ(z)(i z) = Dφ(z)(i z) p(z) + i (i - j) φ p`
  (`weightDeriv_I_mul_self`).
