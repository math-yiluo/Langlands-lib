import Langlands.LocalField.AddValuationUnitFiltration
import Langlands.LocalField.LogAdditiveValuation
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith

/-! # Openness of real-depth logarithmic congruence subgroups -/

noncomputable section

universe u

open scoped NNReal

namespace Langlands.LocalField

/-- A finite logarithmic lower bound is an ordinary positive-radius norm bound. -/
theorem le_negativeLogValue_iff {c : ℝ} (hc : 0 < c) (r : ℝ) (a : ℝ≥0) :
    (r : WithTop ℝ) ≤ negativeLogValue c a ↔ (a : ℝ) ≤ Real.exp (-c * r) := by
  by_cases ha : a = 0
  · subst a
    simp only [NNReal.coe_zero, negativeLogValue_zero, le_top, true_iff]
    exact (Real.exp_pos _).le
  rw [negativeLogValue_of_ne_zero c ha, WithTop.coe_le_coe,
    le_div_iff₀ hc, ← Real.log_le_iff_le_exp (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha))]
  constructor <;> intro h <;> linarith

/-- The normalized negative logarithm vanishes precisely at value one. -/
theorem negativeLogValue_eq_zero_iff {c : ℝ} (hc : 0 < c) (a : ℝ≥0) :
    negativeLogValue c a = 0 ↔ a = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · apply (negativeLogValue_le_iff hc 1 a).mp
      simp only [negativeLogValue_one, h, le_refl]
    · apply (negativeLogValue_le_iff hc a 1).mp
      simp only [negativeLogValue_one, h, le_refl]
  · rintro rfl
    exact negativeLogValue_one c

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Logarithmic congruence is the intersection of a unit sphere and a closed
ball about one, pulled back to field units. -/
theorem addValuationUnitFiltration_log_eq (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    (addValuationUnitFiltration (logAdditiveValuation (NormedField.valuation (K := K))
      c hc) r : Set Kˣ) =
      Units.val ⁻¹' (Metric.sphere (0 : K) 1 ∩
        Metric.closedBall (1 : K) (Real.exp (-c * (r : ℝ)))) := by
  ext x
  change x ∈ addValuationUnitFiltration _ r ↔ _
  rw [mem_addValuationUnitFiltration]
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_sphere,
    Metric.mem_closedBall, dist_eq_norm, sub_zero, logAdditiveValuation_apply,
    NormedField.valuation_apply, negativeLogValue_eq_zero_iff hc,
    le_negativeLogValue_iff hc, ← NNReal.coe_eq_one, coe_nnnorm]

/-- Every real-depth logarithmic congruence subgroup is open in the field-unit
topology, including depth zero. -/
theorem isOpen_addValuationUnitFiltration_log (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    IsOpen (addValuationUnitFiltration
      (logAdditiveValuation (NormedField.valuation (K := K)) c hc) r : Set Kˣ) := by
  rw [addValuationUnitFiltration_log_eq c hc r]
  exact ((IsUltrametricDist.isOpen_sphere (0 : K) one_ne_zero).inter
    (IsUltrametricDist.isOpen_closedBall (1 : K) (Real.exp_ne_zero _))).preimage
      Units.continuous_val

end Langlands.LocalField
