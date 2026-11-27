import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-! # Inversion invariance for a left-invariant probability measure -/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace Langlands.Analysis

/-- A left-invariant probability measure on a measurable group is invariant under inversion. -/
def ProbabilityInvariantInversionStatement.{u} : Prop :=
  ∀ (G : Type u) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant], μ.IsInvInvariant

theorem probabilityInvariantInversion.{u} : ProbabilityInvariantInversionStatement.{u} := by
  intro G _ _ _ _ μ _ _
  have heq (f : G → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x⁻¹ ∂μ) = ∫⁻ x, f x ∂μ := by
    have h : Measurable (fun p : G × G => f (p.1⁻¹ * p.2)) :=
      hf.comp (measurable_fst.inv.mul measurable_snd)
    calc
      _ = ∫⁻ y, ∫⁻ x, f (x⁻¹ * y) ∂μ ∂μ := by
        have hy (y : G) : (∫⁻ x, f (x⁻¹ * y) ∂μ) = ∫⁻ x, f x⁻¹ ∂μ := calc
          _ = ∫⁻ x, f ((y * x)⁻¹ * y) ∂μ := (lintegral_mul_left_eq_self _ y).symm
          _ = _ := by simp only [mul_inv_rev, inv_mul_cancel_right]
        simp only [hy, lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ x, ∫⁻ y, f (x⁻¹ * y) ∂μ ∂μ :=
        (lintegral_lintegral_swap (f := fun x y => f (x⁻¹ * y)) h.aemeasurable).symm
      _ = _ := by simp only [lintegral_mul_left_eq_self, lintegral_const, measure_univ, mul_one]
  constructor
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hs
  change Measure.map Inv.inv μ s = μ s
  rw [← lintegral_indicator_one (μ := Measure.map Inv.inv μ) hs,
    lintegral_map hf measurable_inv, heq _ hf, lintegral_indicator_one hs]

end Langlands.Analysis
