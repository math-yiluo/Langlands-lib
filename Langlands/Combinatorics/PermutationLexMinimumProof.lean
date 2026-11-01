import Langlands.Combinatorics.PermutationLexMinimumStatement
import Mathlib.Data.Finset.Max

/-! # Selecting a least realized permutation -/

namespace Langlands.Combinatorics

/-- Finite enumeration suffices even when the full predicate has infinite support. -/
theorem permutationLexMinimum : PermutationLexMinimum := by
  classical
  intro P w₀ h₀
  let S : Finset (List ℤ) := w₀.permutations.toFinset.filter P
  have hS : S.Nonempty := by
    exact ⟨w₀, by simp [S, List.mem_permutations, h₀]⟩
  let w := S.min' hS
  have hw : w ∈ S := Finset.min'_mem S hS
  obtain ⟨hwperm, hwP⟩ := Finset.mem_filter.mp hw
  refine ⟨w, hwP, List.mem_permutations.mp (List.mem_toFinset.mp hwperm), ?_⟩
  intro v hvP hvperm hlt
  have hv : v ∈ S := Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr (List.mem_permutations.mpr hvperm), hvP⟩
  exact (not_lt_of_ge (Finset.min'_le S v hv)) hlt

end Langlands.Combinatorics
