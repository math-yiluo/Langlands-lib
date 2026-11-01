import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Integrability from a contracting scalar recurrence -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe uX

variable {X : Type uX}

/-- A scalar finite difference along a specified map. -/
def geometricDifference (T : X → X) (r : ℂ) (H : X → ℂ) : X → ℂ :=
  fun x => H x - r * H (T x)

/-- Finite telescoping requires no convergence assumption. -/
theorem sum_geometricDifference (T : X → X) (r : ℂ) (H : X → ℂ)
    (N : ℕ) (x : X) :
    ∑ k ∈ Finset.range N, r ^ k * geometricDifference T r H (T^[k] x) =
      H x - r ^ N * H (T^[N] x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [geometricDifference, Function.iterate_succ_apply', pow_succ]
    ring

section Measure

variable [MeasurableSpace X] (μ : Measure X)

/-- If every orbit reaches a zero of `H`, the integrable finite difference
controls the whole function whenever the scalar ratio has norm below one. -/
theorem integrable_of_geometricDifference
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (r : ℂ) (hr : ‖r‖ < 1) (H : X → ℂ) (hH : Measurable H)
    (hD : Integrable (geometricDifference T r H) μ)
    (hzero : ∀ x, ∃ N : ℕ, H (T^[N] x) = 0) :
    Integrable H μ := by
  let D := geometricDifference T r H
  have hDm : Measurable D :=
    hH.sub (measurable_const.mul (hH.comp hT.measurable))
  have hbound (x : X) :
      ‖H x‖ₑ ≤ ∑' k : ℕ, ‖r ^ k * D (T^[k] x)‖ₑ := by
    obtain ⟨N, hN⟩ := hzero x
    have heq := sum_geometricDifference T r H N x
    rw [hN, mul_zero, sub_zero] at heq
    rw [← heq]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  have hsum :
      (∫⁻ x, ∑' k : ℕ, ‖r ^ k * D (T^[k] x)‖ₑ ∂μ) =
        (∑' k : ℕ, ‖r‖ₑ ^ k) * ∫⁻ x, ‖D x‖ₑ ∂μ := by
    have hm (k : ℕ) : AEMeasurable (fun x => ‖r ^ k * D (T^[k] x)‖ₑ) μ :=
      (measurable_const.mul (hDm.comp (hT.iterate k).measurable)).enorm.aemeasurable
    rw [lintegral_tsum hm]
    calc
      (∑' k : ℕ, ∫⁻ x, ‖r ^ k * D (T^[k] x)‖ₑ ∂μ) =
          ∑' k : ℕ, ‖r‖ₑ ^ k * ∫⁻ x, ‖D x‖ₑ ∂μ := by
        apply tsum_congr
        intro k
        simp only [enorm_mul, enorm_pow]
        calc
          _ = ‖r‖ₑ ^ k * ∫⁻ x, ‖D (T^[k] x)‖ₑ ∂μ :=
            lintegral_const_mul _ (hDm.enorm.comp (hT.iterate k).measurable)
          _ = _ := by rw [(hT.iterate k).lintegral_comp hDm.enorm]
      _ = _ := ENNReal.tsum_mul_right
  have hr' : ‖r‖ₑ < 1 := by
    change (‖r‖₊ : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞)
    exact ENNReal.coe_lt_coe.mpr hr
  refine ⟨hH.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  apply (lintegral_mono hbound).trans_lt
  rw [hsum]
  exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr hr')
    (hasFiniteIntegral_iff_enorm.mp hD.hasFiniteIntegral)

/-- The integral of the whole function is the integral of its difference
divided by the geometric denominator. -/
theorem integral_eq_div_of_geometricDifference
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ)
    (r : ℂ) (hr : ‖r‖ < 1) (H : X → ℂ) (hH : Measurable H)
    (hD : Integrable (geometricDifference T r H) μ)
    (hzero : ∀ x, ∃ N : ℕ, H ((T : X → X)^[N] x) = 0) :
    Integrable H μ ∧
      (∫ x, H x ∂μ) = (∫ x, geometricDifference T r H x ∂μ) / (1 - r) := by
  have hHi := integrable_of_geometricDifference μ T hT r hr H hH hD hzero
  have hcomp := hT.integrable_comp_of_integrable hHi
  have heq :
      (∫ x, geometricDifference T r H x ∂μ) = (1 - r) * ∫ x, H x ∂μ := by
    calc
      _ = (∫ x, H x ∂μ) - ∫ x, r * H (T x) ∂μ :=
        integral_sub hHi (hcomp.const_mul r)
      _ = _ := by
        rw [integral_const_mul, hT.integral_comp' H]
        ring
  have hr0 : 1 - r ≠ 0 := by
    intro h
    have hr1 : r = 1 := (sub_eq_zero.mp h).symm
    simp [hr1] at hr
  refine ⟨hHi, (eq_div_iff hr0).mpr ?_⟩
  exact (mul_comm _ _).trans heq.symm

end Measure

end Langlands.GodementJacquet
