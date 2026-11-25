# Sub-mean-value inequalities for `log⁺ ‖g‖`

Module `Langlands.Analysis.SeveralComplex.Hartogs.SubMeanValue`, namespace
`Langlands.Analysis.SeveralComplex`. This module supports Hartogs' lemma
(`Langlands.Analysis.SeveralComplex.Hartogs.HartogsLemma`). That lemma is a step in the proof of
Hartogs' theorem on separately holomorphic functions, which the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement` needs.

## Provenance

This is internal infrastructure, not a result quoted from a particular source. The two
inequalities are the classical sub-mean-value property of the plurisubharmonic function
`log⁺ ‖g‖` for holomorphic `g`. They are proved here only in the form needed later. Here
`log⁺ = Real.posLog`, that is, `log⁺ t = max 0 (log t)`.

## Statements

* `posLog_norm_le_circleAverage`: let `0 < R` and let `g : ℂ → ℂ` be analytic on a neighbourhood
  of every point of `closedBall c R` (`AnalyticOnNhd`). Then
  `log⁺ ‖g c‖ ≤ circleAverage (fun z => log⁺ ‖g z‖) c R`.

From here on, `E` is a finite-dimensional complex normed space with a measurable structure that
is its Borel σ-algebra, and `μ` is an additive Haar measure on `E`.

* `measurePreserving_smul_of_norm_eq_one`: for `a : ℂ` with `‖a‖ = 1`, the map `x ↦ a • x`
  preserves `μ`.
* `setIntegral_ball_smul_of_norm_eq_one`: for such `a`, any `h : E → ℝ` and any radius `r`,
  `∫ x in ball 0 r, h (a • x) ∂μ = ∫ x in ball 0 r, h x ∂μ`.
* `setIntegral_ball_add`: `∫ x in ball 0 r, h (z + x) ∂μ = ∫ x in ball z r, h x ∂μ`. Only the
  normed group structure of `E` is used here.
* `measureReal_ball_mul_posLog_norm_le` (**ball sub-mean-value inequality**): let `U ⊆ E` be
  open, `g : E → ℂ` holomorphic (`DifferentiableOn ℂ`) on `U`, `0 < r` and
  `closedBall z r ⊆ U`. Then
  `μ.real (ball z r) * log⁺ ‖g z‖ ≤ ∫ x in ball z r, log⁺ ‖g x‖ ∂μ`.

## Proofs

* `posLog_norm_le_circleAverage`: the circle average of `log⁺ ‖g‖` is nonnegative. So we may
  assume `g c ≠ 0`, and we must show `log ‖g c‖ ≤ circleAverage (log⁺ ‖g‖)`. Mathlib's Jensen
  formula (`AnalyticOnNhd.circleAverage_log_norm`) writes `circleAverage (log ‖g‖)` as
  `log ‖g c‖` plus a finite sum. The sum runs over the zeros `u` in the closed disc, with
  nonnegative multiplicities and terms `log (R / ‖c - u‖) ≥ 0`. So
  `log ‖g c‖ ≤ circleAverage (log ‖g‖) ≤ circleAverage (log⁺ ‖g‖)`.
* `measurePreserving_smul_of_norm_eq_one`: `x ↦ a • x` is an `ℝ`-linear automorphism, so it
  maps `μ` to a constant multiple of `μ` (`Measure.map_linearMap_addHaar_eq_smul_addHaar`). It
  maps the unit ball onto itself, and the unit ball has finite positive measure. Hence the
  constant is `1`.
* `setIntegral_ball_smul_of_norm_eq_one` and `setIntegral_ball_add`: change of variables along
  the measure-preserving embeddings `x ↦ a • x` and `x ↦ z + x`. Both maps carry the relevant
  ball onto the other ball in the statement.
* `measureReal_ball_mul_posLog_norm_le`: put `u = log⁺ ‖g‖` and
  `F (x, θ) = u (z + e^{iθ} • x)`. Then `F` is continuous on the compact set
  `closedBall 0 r × [0, 2π]`, hence integrable on `ball 0 r × (0, 2π]`. Fix `x ∈ ball 0 r`. The
  function `ζ ↦ g (z + ζ • x)` is holomorphic near the closed unit disc. The circle inequality
  then gives `u z ≤ (2π)⁻¹ ∫_{(0, 2π]} F (x, θ) dθ`. Integrate this over `x ∈ ball 0 r` and
  swap the integrals (Fubini, `integral_integral_swap`). For each `θ`, the rotation and
  translation invariance above show that `∫ x in ball 0 r, F (x, θ) ∂μ` equals
  `∫ x in ball z r, u x ∂μ`. This yields
  `μ.real (ball 0 r) * u z ≤ ∫ x in ball z r, u x ∂μ`. Finally,
  `μ.real (ball 0 r) = μ.real (ball z r)`.
