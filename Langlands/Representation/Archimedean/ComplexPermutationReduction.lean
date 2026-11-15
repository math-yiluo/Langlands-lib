import Langlands.Representation.Archimedean.ComplexPermutationSwap

/-!
# Permutation invariance from adjacent swaps

`complexStandardPermutation_of_swapJacquet` derives `ComplexStandardPermutationStatement` from
rank-one Jacquet functionals (`SwapJacquetStatement`) and Frobenius reciprocity
(`ComplexJacquetFrobeniusStatement`). A permutation of lists is built from adjacent swaps
(induction on `List.Perm`, keeping track of an unchanged prefix); each swap is handled by
`exists_bijective_swap`; bijective intertwining maps carry irreducibility back
(`isIrreducibleGKModule_of_injective`) and compose (`IsComplexStandardIntertwining.comp`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexPermutation

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

/-- The relation proved by induction: after any prefix, if the standard module of `pre ++ l₁`
is irreducible, the standard module of `pre ++ l₂` maps bijectively and intertwiningly onto
it. -/
def SwapReachable (n : ℕ) (l₁ l₂ : List ComplexCharacterData) : Prop :=
  ∀ pre : List ComplexCharacterData, (pre ++ l₁).length = n →
    IsIrreducibleGKModule (complexStandardRep n (pre ++ l₁)) (complexStandardLie n (pre ++ l₁)) →
      ∃ T : (KF n (pre ++ l₂)) →ₗ[ℂ] (KF n (pre ++ l₁)), Function.Bijective T ∧
        IsComplexStandardIntertwining n (complexStandardRep n (pre ++ l₁))
          (complexStandardLie n (pre ++ l₁)) (pre ++ l₂) T

theorem swapReachable_of_perm (hJ : SwapJacquetStatement)
    (hFR : ComplexJacquetFrobeniusStatement.{0}) (n : ℕ) {l₁ l₂ : List ComplexCharacterData}
    (h : l₁.Perm l₂) : SwapReachable n l₁ l₂ := by
  induction h with
  | nil =>
    intro pre _ _
    exact ⟨LinearMap.id, Function.bijective_id, isComplexStandardIntertwining_id n _⟩
  | @cons x t₁ t₂ _ ih =>
    intro pre hlen hirr
    have e₁ : pre ++ x :: t₁ = (pre ++ [x]) ++ t₁ := by simp
    have e₂ : pre ++ x :: t₂ = (pre ++ [x]) ++ t₂ := by simp
    rw [e₁] at hlen hirr ⊢
    rw [e₂]
    exact ih (pre ++ [x]) hlen hirr
  | swap x y l =>
    intro pre hlen hirr
    exact exists_bijective_swap hJ hFR pre l y x hlen hirr
  | @trans m₁ m₂ m₃ h₁₂ _ ih₁₂ ih₂₃ =>
    intro pre hlen hirr
    obtain ⟨T₁, hT₁bij, hT₁⟩ := ih₁₂ pre hlen hirr
    have hlen₂ : (pre ++ m₂).length = n := by
      rw [List.length_append, ← h₁₂.length_eq, ← List.length_append]
      exact hlen
    have hnt : Nontrivial (KF n (pre ++ m₂)) := by
      have := hirr.1
      exact hT₁bij.2.nontrivial
    have hirr₂ := isIrreducibleGKModule_of_injective hirr hT₁ hT₁bij.1 hnt
    obtain ⟨T₂, hT₂bij, hT₂⟩ := ih₂₃ pre hlen₂ hirr₂
    refine ⟨T₁ ∘ₗ T₂, hT₁bij.comp hT₂bij, ?_⟩
    exact hT₂.comp T₁ (fun k v => hT₁.map_rep k v) (fun X v => hT₁.map_lie (1 ⊗ₜ X) v)

/-- **Permutation invariance**, from rank-one Jacquet functionals and Frobenius
reciprocity. -/
theorem complexStandardPermutation_of_swapJacquet (hJ : SwapJacquetStatement)
    (hFR : ComplexJacquetFrobeniusStatement.{0}) : ComplexStandardPermutationStatement := by
  intro n ds es hlen hperm hirr
  exact swapReachable_of_perm hJ hFR n hperm.symm [] hlen hirr

end Langlands.Archimedean.ComplexPermutation
