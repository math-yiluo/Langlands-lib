import Langlands.Analysis.SeveralComplex.Hartogs.SubMeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Hartogs' lemma on sequences of holomorphic functions

Let `g k` be holomorphic functions on an open subset `U` of a finite-dimensional complex normed
space with `‖g k‖ ≤ A * T ^ k` on `U`, and suppose that at every point of `U` eventually
`‖g k‖ ≤ 1`. Then the growth of `g k` is locally uniformly subexponential:
for every `x₀ ∈ U` and `ε > 0` there is a ball around `x₀` on which eventually
`‖g k‖ ≤ exp ((k + 1) ε)`.

This is the special case of Hartogs' lemma on subharmonic functions
(for the subharmonic functions `log⁺ ‖g k‖ / (k + 1)`) used in the proof of Hartogs' theorem on
separately holomorphic functions. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter MeasureTheory Real
open scoped Topology

/-- `‖a‖ ≤ exp (log⁺ ‖a‖)`. -/
theorem norm_le_exp_posLog_norm (a : ℂ) : ‖a‖ ≤ exp (posLog ‖a‖) := by
  rcases le_or_gt ‖a‖ 1 with h | h
  · exact h.trans (one_le_exp posLog_nonneg)
  · rw [posLog_eq_log (by rw [abs_norm]; exact h.le), exp_log (one_pos.trans h)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Hartogs' lemma** for the functions `log⁺ ‖g k‖ / (k + 1)`. -/
theorem exists_ball_eventually_norm_le_exp {U : Set E} (hU : IsOpen U) {g : ℕ → E → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {A T : ℝ}
    (hb : ∀ k, ∀ x ∈ U, ‖g k x‖ ≤ A * T ^ k)
    (hlim : ∀ x ∈ U, ∀ᶠ k in atTop, ‖g k x‖ ≤ 1)
    {x₀ : E} (hx₀ : x₀ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ k in atTop, ∀ y ∈ ball x₀ δ, ‖g k y‖ ≤ exp ((k + 1) * ε) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar with hμ
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r : ℝ := r₀ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hsub2 : closedBall x₀ (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hr₀U
  set L : ℝ := posLog A + posLog T with hL
  -- `u k = log⁺ ‖g k‖ / (k + 1)`
  set u : ℕ → E → ℝ := fun k x => posLog ‖g k x‖ / (k + 1) with hu_def
  have hu_nonneg : ∀ k x, 0 ≤ u k x := fun k x => div_nonneg posLog_nonneg (by positivity)
  have hu_le : ∀ k, ∀ x ∈ U, u k x ≤ L := by
    intro k x hx
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [hu_def, div_le_iff₀ hk]
    have h1 : posLog ‖g k x‖ ≤ posLog (A * T ^ k) :=
      posLog_le_posLog (by linarith [norm_nonneg (g k x)]) (hb k x hx)
    have h2 : posLog (A * T ^ k) ≤ posLog A + k * posLog T := by
      calc posLog (A * T ^ k) ≤ posLog A + posLog (T ^ k) := posLog_mul
        _ = posLog A + k * posLog T := by rw [posLog_pow]
    have hA0 : 0 ≤ posLog A := posLog_nonneg
    have hT0 : 0 ≤ posLog T := posLog_nonneg
    nlinarith
  have hu_cont : ∀ k, ContinuousOn (fun x => posLog ‖g k x‖) U := fun k =>
    continuous_posLog.comp_continuousOn (continuous_norm.comp_continuousOn (hg k).continuousOn)
  -- the averages over `ball x₀ (2r)` tend to zero (dominated convergence)
  have hlimI : Tendsto (fun k => ∫ x in ball x₀ (2 * r), u k x ∂μ) atTop (𝓝 0) := by
    have h0 : (∫ _x in ball x₀ (2 * r), (0 : ℝ) ∂μ) = 0 := integral_zero _ _
    rw [← h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => L) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact (((hu_cont k).div_const _).mono
        (ball_subset_closedBall.trans hsub2)).aestronglyMeasurable measurableSet_ball
    · exact integrableOn_const measure_ball_lt_top.ne
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg k x)]
      exact hu_le k x (hsub2 (ball_subset_closedBall hx))
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x (hsub2 (ball_subset_closedBall hx))] with k hk
      have : posLog ‖g k x‖ = 0 := (posLog_eq_zero_iff _).2 (by rwa [abs_norm])
      simp [hu_def, this]
  -- the volume of the balls of radius `r`
  set V : ℝ := μ.real (ball (0 : E) r) with hV
  have hVpos : 0 < V :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  have hεV : 0 < V * ε := mul_pos hVpos hε
  refine ⟨r, hr, ?_⟩
  filter_upwards [(tendsto_order.1 hlimI).2 _ hεV] with k hk y hy
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  -- sub-mean-value inequality at `y`, then enlarge the ball
  have hball : closedBall y r ⊆ U := by
    refine (closedBall_subset_closedBall' ?_).trans hsub2
    rw [mem_ball] at hy
    linarith
  have hsm := measureReal_ball_mul_posLog_norm_le μ hU (hg k) hr hball
  rw [Measure.addHaar_real_ball_center μ y r] at hsm
  have hsubB : ball y r ⊆ ball x₀ (2 * r) := by
    intro x hx
    rw [mem_ball] at hx hy ⊢
    linarith [dist_triangle x y x₀]
  have hmono : ∫ x in ball y r, posLog ‖g k x‖ ∂μ ≤ ∫ x in ball x₀ (2 * r), posLog ‖g k x‖ ∂μ := by
    refine setIntegral_mono_set ?_ ?_ hsubB.eventuallyLE
    · exact (((hu_cont k).mono hsub2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall
    · exact ae_restrict_of_forall_mem measurableSet_ball fun x _ => posLog_nonneg
  have hdiv : ∫ x in ball x₀ (2 * r), u k x ∂μ =
      (∫ x in ball x₀ (2 * r), posLog ‖g k x‖ ∂μ) / (k + 1) := integral_div _ _
  rw [hdiv, div_lt_iff₀ hk1] at hk
  have hlog : posLog ‖g k y‖ ≤ (k + 1) * ε := by
    have : V * posLog ‖g k y‖ ≤ V * ((k + 1) * ε) := by nlinarith
    exact le_of_mul_le_mul_left this hVpos
  exact (norm_le_exp_posLog_norm _).trans (exp_le_exp.2 hlog)

end Langlands.Analysis.SeveralComplex
