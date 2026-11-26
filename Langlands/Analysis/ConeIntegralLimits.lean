import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrating against the limit of a translated or damped cone -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On a set where the exponent is nonnegative, the damping factor is bounded by one.
Removing it is valid against every integrable test. -/
theorem tendsto_integral_remove_exponential_damping {d : X → ℝ} (hd : AEMeasurable d μ)
    (hNonneg : ∀ᵐ x ∂μ, 0 ≤ d x) {f : X → V} (hf : Integrable f μ) :
    Tendsto (fun t : ℝ => ∫ x, Real.exp (-(t * d x)) • f x ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun t =>
      (Real.continuous_exp.measurable.comp_aemeasurable ((hd.const_mul t).neg)).aestronglyMeasurable.smul
        hf.aestronglyMeasurable
  · filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with t ht
    filter_upwards [hNonneg] with x hx
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (show 0 ≤ t from le_of_lt ht) hx)))
  · refine Eventually.of_forall fun x => ?_
    have ht : Tendsto (fun t : ℝ => Real.exp (-(t * d x)) • f x)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(0 * d x)) • f x)) := by
      exact (show Continuous fun t : ℝ => Real.exp (-(t * d x)) • f x by fun_prop)
        |>.continuousWithinAt
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_smul] using ht

open Classical in
/-- After translation in a direction strictly positive for each defining coordinate,
the oriented cone integrals tend to the full integral when every sign is positive,
and to zero otherwise. The measurable coordinate functions may include fixed shifts. -/
def TranslatedConeIntegralLimitStatement : Prop :=
  ∀ {X V ι : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Finite ι] (μ : Measure X) (ℓ : ι → X → ℝ) (v ε : ι → ℝ),
    (∀ i, Measurable (ℓ i)) → (∀ i, 0 < v i) →
    ∀ {f : X → V}, Integrable f μ →
      Tendsto (fun n : ℕ => ∫ x in {x | ∀ i, 0 < (ℓ i x + n * v i) * ε i}, f x ∂μ)
        atTop (𝓝 (if ∀ i, 0 < ε i then ∫ x, f x ∂μ else 0))

theorem translatedConeIntegralLimit : TranslatedConeIntegralLimitStatement := by
  classical
  intro X V ι _ _ _ _ μ ℓ v ε hMeas hv f hf
  let C (n : ℕ) : Set X := {x | ∀ i, 0 < (ℓ i x + n * v i) * ε i}
  let F (x : X) : V := if ∀ i, 0 < ε i then f x else 0
  have hC (n : ℕ) : MeasurableSet (C n) := by
    have hEq : C n = ⋂ i, {x | 0 < (ℓ i x + n * v i) * ε i} := by
      ext x
      simp [C]
    rw [hEq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (((hMeas i).add_const _).mul_const _)
  have hEventually (x : X) : (fun n => (C n).indicator f x) =ᶠ[atTop] (fun _ => F x) := by
    have hPos : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < ℓ i x + n * v i := by
      apply eventually_all.mpr
      intro i
      obtain ⟨k, hk⟩ := exists_nat_gt (-ℓ i x / v i)
      filter_upwards [eventually_ge_atTop k] with n hn
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
      linarith [(div_lt_iff₀ (hv i)).mp (hk.trans_le hkn)]
    filter_upwards [hPos] with n hn
    have hmem : x ∈ C n ↔ ∀ i, 0 < ε i := by
      change (∀ i, 0 < (ℓ i x + n * v i) * ε i) ↔ _
      exact forall_congr' fun i => mul_pos_iff_of_pos_left (hn i)
    simp only [Set.indicator_apply, hmem, F]
  have hlim := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator (hC n)) hf.norm
    (fun n => ae_of_all μ fun x => by
      by_cases h : x ∈ C n
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])
    (ae_of_all μ fun x => tendsto_const_nhds.congr' (hEventually x).symm)
  have hInt : (∫ x, F x ∂μ) = if ∀ i, 0 < ε i then ∫ x, f x ∂μ else 0 := by
    split_ifs with h <;> simp [F, h]
  rw [hInt] at hlim
  simpa only [integral_indicator (hC _), C] using hlim

end Langlands.Analysis
