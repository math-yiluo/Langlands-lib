import Mathlib.NumberTheory.LocalField.Basic

/-!
# Nonzero parameters in neighborhoods of zero

The topology is the given valuative topology. Nontriviality supplies a
strictly smaller nonzero value inside every valuation ball.
-/

open Filter Topology

namespace Langlands.LocalField

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsValuativeTopology F] [ValuativeRel.IsNontrivial F]

/-- Every neighborhood of zero contains a nonzero field element. -/
theorem exists_nonzero_mem_of_mem_nhds_zero {V : Set F} (hV : V ∈ 𝓝 (0 : F)) :
    ∃ t : F, t ≠ 0 ∧ t ∈ V := by
  obtain ⟨γ, hγ, hγV⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hV
  obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (γ * δ)
  have ht0 : t ≠ 0 := by
    intro h
    have hz : (0 : ValuativeRel.ValueGroupWithZero F) = γ * δ := by
      simpa [h] using ht
    exact mul_ne_zero hγ hδ0.ne' hz.symm
  refine ⟨t, ht0, hγV ?_⟩
  change ValuativeRel.valuation F t < γ
  rw [ht]
  exact mul_lt_of_lt_one_right (zero_lt_iff.mpr hγ) hδ1

/-- Zero is an accumulation point of the nonzero field elements. -/
theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : F)).NeBot := by
  refine nhdsWithin_neBot.mpr ?_
  intro V hV
  obtain ⟨t, ht0, htV⟩ := exists_nonzero_mem_of_mem_nhds_zero F hV
  exact ⟨t, htV, by simpa using ht0⟩

/-- Select a unit whose underlying field element belongs to a neighborhood of zero. -/
noncomputable def nonzeroParameter (V : Set F) (hV : V ∈ 𝓝 (0 : F)) :
    {t : Fˣ // (t : F) ∈ V} := by
  classical
  let h := exists_nonzero_mem_of_mem_nhds_zero F hV
  exact ⟨Units.mk0 (Classical.choose h) (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

end Langlands.LocalField
