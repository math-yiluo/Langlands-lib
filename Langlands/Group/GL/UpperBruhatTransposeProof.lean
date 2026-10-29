import Langlands.Group.GL.UpperBruhatTransposeStatement

/-!
# Proof of the Weyl-conjugated transpose transport of upper Bruhat cells

The transpose index preserves the inversion count by an explicit bijection of
inverted pairs. The map `g ↦ weylLong * gᵀ * weylLong` is an involutive
anti-automorphism that preserves the upper triangular subgroup and sends the
permutation matrix of `w` to that of the transpose index; this gives the cell
inclusion, and involutivity upgrades every inclusion to an equality.
-/

namespace Langlands.GeneralLinear

open Langlands.HarmonicAnalysis.Distribution

universe u

section Count

variable (n : ℕ)

/-- The transpose index preserves the inversion count: the inverted pairs `(a, b)` of
the transpose index correspond to the inverted pairs `(w⁻¹ a.rev, w⁻¹ b.rev)` of `w`. -/
theorem permutationInversionCount_upperBruhatTransposeIndex (w : Equiv.Perm (Fin n)) :
    permutationInversionCount n (upperBruhatTransposeIndex n w) =
      permutationInversionCount n w := by
  rw [permutationInversionCount_eq_fintypeCard, permutationInversionCount_eq_fintypeCard]
  refine Fintype.card_congr
    { toFun := fun p => ⟨(w⁻¹ p.1.1.rev, w⁻¹ p.1.2.rev), ?_⟩
      invFun := fun q => ⟨((w q.1.1).rev, (w q.1.2).rev), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨⟨a, b⟩, hab, hv⟩ := p
    simp only [upperBruhatTransposeIndex_apply, Fin.rev_lt_rev] at hv
    refine ⟨hv, ?_⟩
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Fin.rev_lt_rev]
    exact hab
  · obtain ⟨⟨x, y⟩, hxy, hw⟩ := q
    refine ⟨Fin.rev_lt_rev.mpr hw, ?_⟩
    simp only [upperBruhatTransposeIndex_apply, Fin.rev_rev, Fin.rev_lt_rev,
      Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    exact hxy
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Fin.rev_rev]
  · rintro ⟨⟨x, y⟩, h⟩
    simp only [Fin.rev_rev, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]

end Count

section Image

variable {α ι : Type*} {f : α → α} {T : ι → ι} {S : ι → Set α}

/-- For an involution `f` of the ambient type and an involution `T` of the index set,
the inclusions `f '' S i ⊆ S (T i)` for all indices are equalities. -/
theorem image_eq_of_involutive_of_image_subset (hf : Function.Involutive f)
    (hT : Function.Involutive T) (h : ∀ i, f '' S i ⊆ S (T i)) (i : ι) :
    f '' S i = S (T i) := by
  refine (h i).antisymm fun x hx => ⟨f x, ?_, hf x⟩
  simpa only [hT i] using h (T i) ⟨x, hx, rfl⟩

end Image

section Transport

variable (n : ℕ) (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The statement's homeomorphism is `g ↦ weylLong * gᵀ * weylLong`. -/
theorem weylConjugateTranspose_apply (g : Langlands.GeneralLinear n R) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) g =
      weylLong n R * transposeHomeomorph n R g * weylLong n R := by
  rw [Homeomorph.trans_apply, conjugationHomeomorph_apply, weylLong_inv]

/-- Its entry `(i, j)` is `g j.rev i.rev`. -/
theorem weylConjugateTranspose_entry (g : Langlands.GeneralLinear n R) (i j : Fin n) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) g i j =
      g j.rev i.rev := by
  rw [weylConjugateTranspose_apply, weylLong_conjugate_entry, transposeHomeomorph_entry]

/-- The map is an involution. -/
theorem weylConjugateTranspose_involutive :
    Function.Involutive
      ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) := by
  intro g
  apply Units.ext
  ext i j
  rw [weylConjugateTranspose_entry, weylConjugateTranspose_entry, Fin.rev_rev, Fin.rev_rev]

/-- The map reverses products. -/
theorem weylConjugateTranspose_mul (g h : Langlands.GeneralLinear n R) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) (g * h) =
      ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) h *
        ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) g := by
  simp only [weylConjugateTranspose_apply, transposeHomeomorph_mul, mul_assoc]
  rw [← mul_assoc (weylLong n R) (weylLong n R), weylLong_mul_self, one_mul]

/-- The map preserves the upper triangular subgroup. -/
theorem weylConjugateTranspose_mem_upperTriangular {b : Langlands.GeneralLinear n R}
    (hb : b ∈ upperTriangularSubgroup n R) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) b ∈
      upperTriangularSubgroup n R := by
  rw [mem_upperTriangularSubgroup_iff] at hb ⊢
  intro i j hji
  rw [weylConjugateTranspose_entry]
  exact hb j.rev i.rev (Fin.rev_lt_rev.mpr hji)

/-- The map sends the permutation matrix of `w` to that of the transpose index. -/
theorem weylConjugateTranspose_permutation (w : Equiv.Perm (Fin n)) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R)))
        (permutation n R w) =
      permutation n R (upperBruhatTransposeIndex n w) := by
  rw [weylConjugateTranspose_apply, permutation_upperBruhatTransposeIndex,
    transposeHomeomorph_apply, permutation_inv, inverseTranspose_permutation]

/-- The map sends the cell of `w` into the cell of the transpose index. -/
theorem weylConjugateTranspose_image_upperBruhatCell_subset (w : Equiv.Perm (Fin n)) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) ''
        upperBruhatCell n R w ⊆
      upperBruhatCell n R (upperBruhatTransposeIndex n w) := by
  rintro _ ⟨g, ⟨b₁, hb₁, b₂, hb₂, rfl⟩, rfl⟩
  refine ⟨_, weylConjugateTranspose_mem_upperTriangular n R hb₂,
    _, weylConjugateTranspose_mem_upperTriangular n R hb₁, ?_⟩
  rw [weylConjugateTranspose_mul, weylConjugateTranspose_mul,
    weylConjugateTranspose_permutation, mul_assoc]

/-- The map sends the cell of `w` onto the cell of the transpose index. -/
theorem weylConjugateTranspose_image_upperBruhatCell (w : Equiv.Perm (Fin n)) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) ''
        upperBruhatCell n R w =
      upperBruhatCell n R (upperBruhatTransposeIndex n w) :=
  image_eq_of_involutive_of_image_subset (weylConjugateTranspose_involutive n R)
    (upperBruhatTransposeIndex_involutive n)
    (weylConjugateTranspose_image_upperBruhatCell_subset n R) w

/-- The map sends each inversion layer onto itself. -/
theorem weylConjugateTranspose_image_upperBruhatLayerLE (k : ℕ) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) ''
        upperBruhatLayerLE n R k =
      upperBruhatLayerLE n R k := by
  refine image_eq_of_involutive_of_image_subset (S := fun _ : Unit => upperBruhatLayerLE n R k)
    (weylConjugateTranspose_involutive n R) (T := id) (fun _ => rfl) ?_ ()
  rintro - _ ⟨g, ⟨v, hv, hg⟩, rfl⟩
  exact ⟨upperBruhatTransposeIndex n v,
    (permutationInversionCount_upperBruhatTransposeIndex n v).trans_le hv,
    weylConjugateTranspose_image_upperBruhatCell_subset n R v ⟨g, hg, rfl⟩⟩

/-- The map sends the higher cells of `w` onto those of the transpose index. -/
theorem weylConjugateTranspose_image_upperBruhatHigherCells (w : Equiv.Perm (Fin n)) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) ''
        upperBruhatHigherCells n R w =
      upperBruhatHigherCells n R (upperBruhatTransposeIndex n w) := by
  refine image_eq_of_involutive_of_image_subset (weylConjugateTranspose_involutive n R)
    (upperBruhatTransposeIndex_involutive n) ?_ w
  rintro w _ ⟨g, ⟨v, hv, hg⟩, rfl⟩
  refine ⟨upperBruhatTransposeIndex n v, ?_,
    weylConjugateTranspose_image_upperBruhatCell_subset n R v ⟨g, hg, rfl⟩⟩
  rwa [permutationInversionCount_upperBruhatTransposeIndex,
    permutationInversionCount_upperBruhatTransposeIndex]

/-- The map sends the cell neighborhood of `w` onto that of the transpose index. -/
theorem weylConjugateTranspose_image_upperBruhatCellNeighborhood (w : Equiv.Perm (Fin n)) :
    ((transposeHomeomorph n R).trans (conjugationHomeomorph (weylLong n R))) ''
        upperBruhatCellNeighborhood n R w =
      upperBruhatCellNeighborhood n R (upperBruhatTransposeIndex n w) := by
  rw [upperBruhatCellNeighborhood, Set.image_union,
    weylConjugateTranspose_image_upperBruhatCell,
    weylConjugateTranspose_image_upperBruhatHigherCells, upperBruhatCellNeighborhood]

end Transport

/-- Proof of `UpperBruhatTransposeStatement`. -/
theorem upperBruhatTranspose : UpperBruhatTransposeStatement.{u} := by
  refine ⟨permutationInversionCount_upperBruhatTransposeIndex, ?_⟩
  intro R _ _ _ n w k
  exact ⟨weylConjugateTranspose_image_upperBruhatCell n R w,
    weylConjugateTranspose_image_upperBruhatLayerLE n R k,
    weylConjugateTranspose_image_upperBruhatHigherCells n R w,
    weylConjugateTranspose_image_upperBruhatCellNeighborhood n R w⟩

end Langlands.GeneralLinear
