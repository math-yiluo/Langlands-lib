import Mathlib.NumberTheory.LocalField.Basic

/-! # Infinitude from a nontrivial valuative relation -/

universe u

namespace Langlands.LocalField

/-- A field with a nontrivial valuative relation is infinite. -/
theorem infinite_of_nontrivialValuativeRel
    (K : Type u) [Field K] [ValuativeRel K] [ValuativeRel.IsNontrivial K] :
    Infinite K := by
  obtain ⟨c, hc0, hc1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective c
  apply Infinite.of_injective (fun n : ℕ => a ^ n)
  intro m n h
  apply pow_right_injective₀ hc0 (ne_of_lt hc1)
  simpa only [map_pow, ha] using congrArg (ValuativeRel.valuation K) h

/-- The local-field hypotheses supply the infinitude needed by rational-point
detection for split tori. -/
theorem infinite_of_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Infinite K :=
  infinite_of_nontrivialValuativeRel K

/-- The arbitrary-universe infinitude interface for nontrivially valued fields. -/
def NontrivialValuationInfiniteStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [ValuativeRel.IsNontrivial K], Infinite K

theorem nontrivialValuationInfinite : NontrivialValuationInfiniteStatement.{u} := by
  intro K _ _ _
  exact infinite_of_nontrivialValuativeRel K

end Langlands.LocalField
