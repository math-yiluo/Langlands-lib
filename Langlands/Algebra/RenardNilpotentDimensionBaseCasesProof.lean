import Langlands.Algebra.RenardNilpotentDimensionBaseCasesStatement
import Langlands.Algebra.CommutingDimensionHelpers

noncomputable section

universe u

namespace Langlands.Renard

variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem one_le_nilpotent_max (l : ℕ) [Nontrivial V] :
    1 ≤ nilpotentGeneratedMaxDimension l V := by
  obtain ⟨a, _, _, ha⟩ := nilpotentGeneratedMaxDimension_attained l V
  rw [← ha]
  exact Module.finrank_pos

private theorem nilpotent_max_finrank_one (l : ℕ)
    (hV : Module.finrank ℂ V = 1) :
    nilpotentGeneratedMaxDimension l V = 1 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  apply le_antisymm
  · simpa only [hV, one_pow] using nilpotentGeneratedMaxDimension_le l V
  · exact one_le_nilpotent_max V l

private theorem nilpotent_max_one_generator :
    nilpotentGeneratedMaxDimension 1 V ≤ Module.finrank ℂ V := by
  obtain ⟨a, _, _, ha⟩ := nilpotentGeneratedMaxDimension_attained 1 V
  rw [← ha, Set.range_unique]
  exact Langlands.CommutingDimension.singleton_dimension ℂ V (a default)

private theorem nilpotent_max_zero_generators :
    nilpotentGeneratedMaxDimension 0 V =
      if Module.finrank ℂ V = 0 then 0 else 1 := by
  classical
  by_cases hV : Module.finrank ℂ V = 0
  · simpa only [hV, ite_true] using
      nilpotentGeneratedMaxDimension_eq_zero_of_finrank_eq_zero 0 V hV
  · let : Nontrivial V :=
      Module.nontrivial_of_finrank_pos (R := ℂ) (Nat.pos_of_ne_zero hV)
    obtain ⟨a, _, _, ha⟩ := nilpotentGeneratedMaxDimension_attained 0 V
    rw [← ha, Set.range_eq_empty, Algebra.adjoin_empty, Subalgebra.finrank_bot]
    simp only [hV, ↓reduceIte]

/-- Renard's numerical base cases for the actual nilpotent-generated maximum. -/
theorem nilpotentDimensionBaseCases : NilpotentDimensionBaseCasesStatement.{u} := by
  refine ⟨?_, nilpotentGeneratedPhi_zero, ?_, ?_, ?_⟩
  · intro V _ _ _
    exact ⟨(fun l hV =>
      nilpotentGeneratedMaxDimension_eq_zero_of_finrank_eq_zero l V hV),
      nilpotent_max_finrank_one V, nilpotent_max_one_generator V,
      nilpotent_max_zero_generators V⟩
  · intro l
    exact nilpotent_max_finrank_one (Fin 1 → ℂ) l (by simp)
  · intro k
    simpa only [nilpotentGeneratedPhi, Module.finrank_fin_fun] using
      nilpotent_max_one_generator (Fin k → ℂ)
  · intro k
    simpa only [nilpotentGeneratedPhi, Module.finrank_fin_fun] using
      nilpotent_max_zero_generators (Fin k → ℂ)

end Langlands.Renard
