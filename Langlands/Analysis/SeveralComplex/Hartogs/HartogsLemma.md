# Hartogs' lemma on sequences of holomorphic functions

Module `Langlands.Analysis.SeveralComplex.Hartogs.HartogsLemma`, namespace
`Langlands.Analysis.SeveralComplex`. This module gives the growth estimate that drives the
extension step `differentiableOn_prod_ball_of_small`
(`Langlands.Analysis.SeveralComplex.Hartogs.TaylorCoefficients`) in the proof of Hartogs'
theorem on separately holomorphic functions (Task 5431).

## Provenance

This is internal infrastructure, not a result quoted from a particular source. Hartogs' lemma is
classical in a more general form: a sequence of subharmonic functions that is locally uniformly
bounded above and has pointwise `limsup ≤ C` satisfies `≤ C + ε` locally uniformly from some
index on. Only the special case used for Hartogs' theorem is stated and proved here. It concerns
the functions `log⁺ ‖g k‖ / (k + 1)` with `g k` holomorphic, where `log⁺ = Real.posLog`. The Lean
statement below is exactly what is proved. It does not formalize subharmonic functions or the
general lemma.

## Statements

* `norm_le_exp_posLog_norm`: for `a : ℂ`, `‖a‖ ≤ exp (log⁺ ‖a‖)`.
* `exists_ball_eventually_norm_le_exp` (**Hartogs' lemma**, special case): let `E` be a
  finite-dimensional complex normed space, `U ⊆ E` open, and `g : ℕ → E → ℂ` with every `g k`
  holomorphic (`DifferentiableOn ℂ`) on `U`. Let `A T : ℝ` with `‖g k x‖ ≤ A * T ^ k` for all
  `k` and all `x ∈ U`. Suppose that for every `x ∈ U`, eventually in `k`, `‖g k x‖ ≤ 1`. Then for
  every `x₀ ∈ U` and every `ε > 0` there is `δ > 0` such that, eventually in `k`,
  `‖g k y‖ ≤ exp ((k + 1) * ε)` for all `y ∈ ball x₀ δ`.

## Proofs

* `norm_le_exp_posLog_norm`: if `‖a‖ ≤ 1` the right side is at least `1`. Otherwise
  `log⁺ ‖a‖ = log ‖a‖`.
* `exists_ball_eventually_norm_le_exp`: equip `E` with its Borel σ-algebra and the additive Haar
  measure `μ = Measure.addHaar`. Choose `r > 0` with `closedBall x₀ (2r) ⊆ U`, and put
  `u k = log⁺ ‖g k‖ / (k + 1)`. From the growth bound,
  `0 ≤ u k ≤ L := log⁺ A + log⁺ T` on `U`, using `log⁺ (a b) ≤ log⁺ a + log⁺ b` and
  `log⁺ (T ^ k) = k log⁺ T`. At each point of `U`, `u k` is eventually `0`. By dominated
  convergence, `∫ x in ball x₀ (2r), u k x ∂μ → 0`. Let `V = μ.real (ball 0 r) > 0`. Take `k`
  so large that this integral is `< V ε`, and let `y ∈ ball x₀ r`. Then
  `closedBall y r ⊆ closedBall x₀ (2r) ⊆ U`. The ball sub-mean-value inequality
  `measureReal_ball_mul_posLog_norm_le` (module `Hartogs.SubMeanValue`) gives
  `V · log⁺ ‖g k y‖ ≤ ∫ x in ball y r, log⁺ ‖g k x‖ ∂μ`. Enlarging the ball to
  `ball x₀ (2r)` and using the choice of `k` gives `V · log⁺ ‖g k y‖ < V (k + 1) ε`. Hence
  `log⁺ ‖g k y‖ ≤ (k + 1) ε`, and the first bullet concludes, with `δ = r`.
