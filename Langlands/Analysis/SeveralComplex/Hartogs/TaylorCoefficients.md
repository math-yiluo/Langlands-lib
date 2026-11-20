# Taylor coefficients and the extension step of Hartogs' theorem

Module `Langlands.Analysis.SeveralComplex.Hartogs.TaylorCoefficients`, namespace
`Langlands.Analysis.SeveralComplex`. The module proves the extension step
`differentiableOn_prod_ball_of_small` of Hartogs' theorem on separately holomorphic functions.
The proof of `Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement`
(Task 5431) needs that theorem.

## Provenance

This is internal infrastructure, not a result quoted from a particular source. The extension
step is the core of the classical proof of Hartogs' theorem (F. Hartogs, *Zur Theorie der
analytischen Funktionen mehrerer unabhängiger Veränderlichen*, Math. Ann. 62 (1906); see also
L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II). There it is
stated for polydiscs in `ℂⁿ`. Here it is stated and proved, as below, for `B × ball w₁ R` with
`B` an arbitrary open subset of a finite-dimensional complex normed space `E₁`. The Lean proof
follows the classical argument: Cauchy estimates, Hartogs' lemma on the Taylor coefficients,
and Osgood's lemma.

## Definition

For `f : E₁ × ℂ → ℂ`, `w₁ : ℂ`, `ρ : ℝ`, `k : ℕ` and `z : E₁`,

`taylorCoeff f w₁ ρ k z = (2πi)⁻¹ • ∮ w in C(w₁, ρ), (1 / (w - w₁) ^ (k + 1)) • f (z, w)`.

For `0 < ρ`, and `w ↦ f (z, w)` holomorphic near the closed disc, this is the `k`-th Taylor
coefficient of `w ↦ f (z, w)` at `w₁` (first statement below).

## Statements

In the first three statements, `E₁` is any type.

* `taylorCoeff_eq`: if `0 < ρ < R` and `w ↦ f (z, w)` is holomorphic on `ball w₁ R`, then
  `taylorCoeff f w₁ ρ k z = (k !)⁻¹ * iteratedDeriv k (fun w => f (z, w)) w₁`.
* `hasSum_taylorCoeff`: under the same hypotheses, for `w ∈ ball w₁ R`, the series
  `∑ k, taylorCoeff f w₁ ρ k z * (w - w₁) ^ k` has sum `f (z, w)`.
* `norm_taylorCoeff_le` (**Cauchy's estimate**): if `0 < ρ` and `‖f (z, w)‖ ≤ M` on
  `sphere w₁ ρ`, then `‖taylorCoeff f w₁ ρ k z‖ ≤ M / ρ ^ k`.

From here on, `E₁` is a finite-dimensional complex normed space and `B ⊆ E₁` is open.

* `differentiableOn_taylorCoeff`: let `0 < ρ`, `ρ < r` and `ρ < R`. Suppose `z ↦ f (z, w)` is
  holomorphic on `B` for every `w ∈ ball w₁ R`, and `f` is continuous on `B × ball w₁ r`. Then
  `taylorCoeff f w₁ ρ k` is holomorphic (`DifferentiableOn ℂ`) on `B`.
* `differentiableOn_prod_ball_of_small` (**extension step of Hartogs' theorem**): let `0 < r`,
  and let `f : E₁ × ℂ → ℂ` satisfy:
  * `z ↦ f (z, w)` is holomorphic on `B` for every `w ∈ ball w₁ R`;
  * `w ↦ f (z, w)` is holomorphic on `ball w₁ R` for every `z ∈ B`;
  * `f` is holomorphic on `B × ball w₁ r`.

  Then `f` is holomorphic on `B × ball w₁ R`.

## Proofs

* `taylorCoeff_eq`: Mathlib's Cauchy integral formula for derivatives
  (`DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`), applied on `closedBall w₁ ρ`.
* `hasSum_taylorCoeff`: Mathlib's Taylor expansion on a disc
  (`Complex.hasSum_taylorSeries_on_ball`), rewritten with `taylorCoeff_eq`.
* `norm_taylorCoeff_le`: the integrand has norm at most `M / ρ ^ (k + 1)` on the circle.
  The standard estimate `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`
  then gives the bound `ρ · M / ρ ^ (k + 1)`.
* `differentiableOn_taylorCoeff`: the integrand `(z, w) ↦ (w - w₁)^{-(k+1)} • f (z, w)` is
  jointly continuous on `B × sphere w₁ ρ`, because the sphere lies in `ball w₁ r`. For each
  `w` on the sphere it is holomorphic in `z`, because the sphere lies in `ball w₁ R`. The
  parametric holomorphy lemma `differentiableOn_circleIntegral_of_continuousOn` (module
  `Langlands.Analysis.SeveralComplex.ParametricHolomorphy`) concludes.
* `differentiableOn_prod_ball_of_small`: by Osgood's lemma
  (`differentiableOn_prod_of_locallyBounded`, module `Hartogs.Osgood`), it suffices to bound
  `‖f‖` near each point `(z₀, w₀) ∈ B × ball w₁ R`. Put `ρ = min r R / 2` and choose
  `‖w₀ - w₁‖ < R₂ < R₁ < R`. Choose `σ > 0` with `closedBall z₀ σ ⊆ B`.
  1. *Cauchy bound.* `f` is continuous on the compact set
     `closedBall z₀ σ × sphere w₁ ρ ⊆ B × ball w₁ r`, so it is bounded there by some `M₀`.
     Cauchy's estimate gives `‖taylorCoeff f w₁ ρ k z‖ ≤ M₀ / ρ ^ k` for `z ∈ closedBall z₀ σ`.
  2. *Hartogs' lemma.* Put `g k z = taylorCoeff f w₁ ρ k z * R₁ ^ k`. By
     `differentiableOn_taylorCoeff`, `g k` is holomorphic on `ball z₀ σ`, and by step 1,
     `‖g k‖ ≤ M₀ (R₁ / ρ) ^ k` there. For each `z`, the Taylor series of `w ↦ f (z, w)`
     converges at `w₁ + R₁ ∈ ball w₁ R`, so `g k z → 0`. Hence eventually `‖g k z‖ ≤ 1`.
     Apply `exists_ball_eventually_norm_le_exp` (module `Hartogs.HartogsLemma`) with
     `ε = log (R₁ / R₂) / 2`. This gives `δ > 0` and `K` with
     `‖taylorCoeff f w₁ ρ k y‖ ≤ exp ((k + 1) ε) / R₁ ^ k` for `k ≥ K` and `y ∈ ball z₀ δ`.
  3. *Summation.* Put `q = exp ε · R₂ / R₁`. Then `q < 1`, because `exp ε < R₁ / R₂`. For
     `y ∈ ball z₀ (min δ σ)` and `w ∈ ball w₁ R₂`, expand `f (y, w)` in its Taylor series
     (`hasSum_taylorCoeff`). Bound the `k`-th term by `M₀ / ρ ^ k · R₂ ^ k` for `k < K`
     (step 1) and by `exp ε · q ^ k` for `k ≥ K` (step 2). The resulting majorant is
     summable and does not depend on `(y, w)`. Its sum bounds `‖f‖` on the neighbourhood
     `ball z₀ (min δ σ) × ball w₁ R₂` of `(z₀, w₀)`.
