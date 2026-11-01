import Langlands.Group.GL.TripleMergeShape
import Langlands.Representation.Parabolic.OrderedTensorOccurrences

/-! Actual triple inner tensors and return after changing the selected block. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.GeneralLinear.BlockShape

open Geometric

variable {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 2 < B.length)
  (δ : ℕ) (hδ : δ ≤ 1)

/-- The selected adjacent swap inside the merged triple; identity on each
outside singleton. -/
def tripleInnerSwap (m : Fin (B.tripleMerge j hj).length) :
    Equiv.Perm (Fin (B.tripleRefinement j hj m).length) :=
  if hm : m.val = j then
    Equiv.swap
      ⟨δ, by rw [tripleRefinement_length, ite_eq_left hm]; omega⟩
      ⟨δ + 1, by rw [tripleRefinement_length, ite_eq_left hm]; omega⟩
  else Equiv.refl _

/-- The inner swap performs exactly the specified global adjacent swap. -/
theorem tripleBlockEquiv_innerSwap (m : Fin (B.tripleMerge j hj).length)
    (k : Fin (B.tripleRefinement j hj m).length) :
    B.tripleBlockEquiv j hj ⟨m, B.tripleInnerSwap j hj δ hδ m k⟩ =
      B.adjacentSwap (j + δ) (by omega) (B.tripleBlockEquiv j hj ⟨m, k⟩) := by
  by_cases hm : m.val = j
  · let a : Fin (B.tripleRefinement j hj m).length :=
      ⟨δ, by rw [tripleRefinement_length, ite_eq_left hm]; omega⟩
    let b : Fin (B.tripleRefinement j hj m).length :=
      ⟨δ + 1, by rw [tripleRefinement_length, ite_eq_left hm]; omega⟩
    have hv := B.tripleBlockEquiv_val j hj ⟨m, k⟩
    have ha := B.tripleBlockEquiv_val j hj ⟨m, a⟩
    have hb := B.tripleBlockEquiv_val j hj ⟨m, b⟩
    rw [tripleInnerSwap, dite_eq_left hm]
    change B.tripleBlockEquiv j hj ⟨m, Equiv.swap a b k⟩ = _
    rw [Equiv.swap_apply_def, adjacentSwap, Equiv.swap_apply_def]
    split_ifs <;> apply Fin.ext <;>
      simp only [Fin.ext_iff] at * <;>
      simp only [hm, lt_irrefl, ite_false, a, b] at * <;> omega
  · have hk : k.val < 1 := (B.tripleRefinement_length_of_ne j hj m hm) ▸ k.isLt
    have hv := B.tripleBlockEquiv_val j hj ⟨m, k⟩
    dsimp only at hv
    rw [tripleInnerSwap, dite_eq_right hm, Equiv.refl_apply]
    symm
    apply Equiv.swap_apply_of_ne_of_ne <;>
      simp only [ne_eq, Fin.ext_iff] <;> split_ifs at hv <;> omega

/-- Permute the inner triple and retain each outside singleton literally. -/
def triplePermutedRefinement : BlockRefinement (B.tripleMerge j hj) := fun m =>
  (B.tripleRefinement j hj m).permute (B.tripleInnerSwap j hj δ hδ m)

/-- The permuted inner ranks have exactly the target global ranks. -/
theorem triplePermuted_size
    (a : (m : Fin (B.tripleMerge j hj).length) ×
      Fin (B.triplePermutedRefinement j hj δ hδ m).length) :
    (B.triplePermutedRefinement j hj δ hδ a.1).size a.2 =
      (B.permute (B.adjacentSwap (j + δ) (by omega))).size
        (B.tripleBlockEquiv j hj a) :=
  congrArg B.size (B.tripleBlockEquiv_innerSwap j hj δ hδ a.1 a.2)

/-- The internal-permutation and direct-rank constructions give the same
actual swapped refinement. -/
theorem triplePermutedRefinement_eq_swap :
    B.triplePermutedRefinement j hj δ hδ = B.tripleSwapRefinement j hj δ hδ := by
  funext m
  apply ext_of_size (B₁ := B.triplePermutedRefinement j hj δ hδ m)
    (B₂ := B.tripleSwapRefinement j hj δ hδ m) rfl
  intro k
  exact congrArg B.size (B.tripleBlockEquiv_innerSwap j hj δ hδ m k)

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 2 < B.length)

/-- All original actual inner tensors, including every outside singleton. -/
def tripleInnerTensor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) →
    ∀ m, SmoothRep.{0, uF, uV} ℂ ((B.tripleRefinement j hj m).Levi F.Carrier) :=
  letI := T.topology
  fun C m => FiniteTensor.externalSmoothObject
    (fun k => C (B.tripleBlockEquiv j hj ⟨m, k⟩))

/-- The actual inner tensors after the selected adjacent triple swap. -/
def triplePermutedTensor (δ : ℕ) (hδ : δ ≤ 1) :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) →
    ∀ m, SmoothRep.{0, uF, uV} ℂ
      ((B.triplePermutedRefinement j hj δ hδ m).Levi F.Carrier) :=
  letI := T.topology
  fun C m => FiniteTensor.externalSmoothObject
    (fun k => C (B.tripleBlockEquiv j hj
      ⟨m, B.tripleInnerSwap j hj δ hδ m k⟩))

private theorem family_rankCast_eq {ι : Sort*} (r : ι → ℕ) {X : ℕ → Sort*}
    (C : ∀ i, X (r i)) {a b : ι} (hab : a = b) (h : r a = r b) :
    (h.symm ▸ C b : X (r a)) = C a := by
  subst b
  rfl

/-- The ordered target factors are the actual internally permuted tensors,
including the exact rank transports of the target family. -/
theorem triplePermutedTensorFactors_eq (δ : ℕ) (hδ : δ ≤ 1) :
    letI := T.topology
    ∀ C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      orderedRefinementTensorFactors F T
        (B.permute (B.adjacentSwap (j + δ) (by omega)))
        (B.tripleMerge j hj) (B.triplePermutedRefinement j hj δ hδ)
        (B.tripleBlockEquiv j hj) (B.triplePermuted_size j hj δ hδ)
        (fun i => C (B.adjacentSwap (j + δ) (by omega) i)) =
      triplePermutedTensor F T B j hj δ hδ C := by
  let := T.topology
  intro C
  funext m
  apply congrArg FiniteTensor.externalSmoothObject
  funext k
  exact family_rankCast_eq B.size
    (X := fun r => SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) C
    (B.tripleBlockEquiv_innerSwap j hj δ hδ m k) (B.triplePermuted_size j hj δ hδ ⟨m, k⟩)

private theorem subquotient_tensor_of_permutation_eq_refl {r : ℕ}
    (D : BlockShape r) (σ : Equiv.Perm (Fin D.length)) (hσ : σ = Equiv.refl _) :
    letI := T.topology
    ∀ (C : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size k) F.Carrier))
      (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C)
        ((T.normalizedJacquetFunctor D).obj E) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun k => C (σ k)))
        ((T.normalizedJacquetFunctor (D.permute σ)).obj E) := by
  let := T.topology
  cases hσ
  exact fun _ _ h => h

/-- Outside the selected triple, every actual occurrence is unchanged. -/
theorem triplePermutedOccurrence_of_ne (δ : ℕ) (hδ : δ ≤ 1)
    (m : Fin (B.tripleMerge j hj).length) (hm : m.val ≠ j) :
    letI := T.topology
    ∀ (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (E : SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.tripleMerge j hj).size m) F.Carrier)),
      SmoothRep.IsSubquotient (tripleInnerTensor F T B j hj C m)
        ((T.normalizedJacquetFunctor (B.tripleRefinement j hj m)).obj E) →
      SmoothRep.IsSubquotient (triplePermutedTensor F T B j hj δ hδ C m)
        ((T.normalizedJacquetFunctor (B.triplePermutedRefinement j hj δ hδ m)).obj E) := by
  let := T.topology
  intro C E h
  have hs : B.tripleInnerSwap j hj δ hδ m = Equiv.refl _ := by
    rw [BlockShape.tripleInnerSwap, dite_eq_right hm]
  exact subquotient_tensor_of_permutation_eq_refl F T (B.tripleRefinement j hj m)
    (B.tripleInnerSwap j hj δ hδ m) hs
    (fun k => C (B.tripleBlockEquiv j hj ⟨m, k⟩)) E h

/-- Extract actual admissible irreducible coarse factors with the original
three-factor occurrence in the selected block and all outside occurrences. -/
theorem exists_tripleCoarseFactors :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      π.IsAdmissible → π.HasFiniteLength →
      (∀ i, (C i).IsIrreducible) → (∀ i, (C i).IsAdmissible) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C)
        ((T.normalizedJacquetFunctor B).obj π) →
      ∃ X : ∀ m, SmoothRep.{0, uF, uV} ℂ
          (GeneralLinear ((B.tripleMerge j hj).size m) F.Carrier),
        (∀ m, (X m).IsIrreducible) ∧
        (∀ m, (X m).IsAdmissible) ∧
        (∀ m, (X m).HasFiniteLength) ∧
        SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
          ((T.normalizedJacquetFunctor (B.tripleMerge j hj)).obj π) ∧
        (∀ m, SmoothRep.IsSubquotient (tripleInnerTensor F T B j hj C m)
          ((T.normalizedJacquetFunctor (B.tripleRefinement j hj m)).obj (X m))) := by
  let := T.topology
  intro π C hπa hπfin hCi hCa hC
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < B.length) B.length_le
  exact exists_factorized_coarseJacquet_of_ordered F T B (B.tripleMerge j hj)
    (B.tripleRefinement j hj) (B.tripleBlockEquiv j hj) (B.tripleBlock_size j hj)
    (fun a b hab => (B.tripleBlockEquiv_lt_iff j hj a b).mpr hab)
    hn π C hπa hπfin hCi hCa hC

/-- A changed actual occurrence in only the selected coarse block gives the
specified global adjacent triple swap. All outside blocks use their original
occurrences, with no irreducibility or finiteness premise in this return. -/
theorem subquotient_tripleSwapJacquet_of_selected (δ : ℕ) (hδ : δ ≤ 1) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (X : ∀ m, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.tripleMerge j hj).size m) F.Carrier))
      (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
        ((T.normalizedJacquetFunctor (B.tripleMerge j hj)).obj π) →
      (∀ m, SmoothRep.IsSubquotient (tripleInnerTensor F T B j hj C m)
        ((T.normalizedJacquetFunctor (B.tripleRefinement j hj m)).obj (X m))) →
      SmoothRep.IsSubquotient
        (triplePermutedTensor F T B j hj δ hδ C (B.tripleMergeIndex j hj))
        ((T.normalizedJacquetFunctor
          (B.triplePermutedRefinement j hj δ hδ (B.tripleMergeIndex j hj))).obj
            (X (B.tripleMergeIndex j hj))) →
      SmoothRep.IsSubquotient
        (FiniteTensor.externalSmoothObject
          (fun i => C (B.adjacentSwap (j + δ) (by omega) i)))
        ((T.normalizedJacquetFunctor
          (B.permute (B.adjacentSwap (j + δ) (by omega)))).obj π) := by
  let := T.topology
  intro π X C hX hblocks hselected
  apply subquotient_orderedJacquet_of_coarse_factors F T
    (B.permute (B.adjacentSwap (j + δ) (by omega))) (B.tripleMerge j hj)
    (B.triplePermutedRefinement j hj δ hδ) (B.tripleBlockEquiv j hj)
    (B.triplePermuted_size j hj δ hδ)
    (fun a b hab => (B.tripleBlockEquiv_lt_iff j hj a b).mpr hab)
    π X (fun i => C (B.adjacentSwap (j + δ) (by omega) i)) hX
  rw [triplePermutedTensorFactors_eq F T B j hj δ hδ C]
  intro m
  by_cases hm : m.val = j
  · have hm' : m = B.tripleMergeIndex j hj := Fin.ext hm
    subst m
    exact hselected
  · exact triplePermutedOccurrence_of_ne F T B j hj δ hδ m hm C (X m) (hblocks m)

end Langlands.CuspidalSupport
