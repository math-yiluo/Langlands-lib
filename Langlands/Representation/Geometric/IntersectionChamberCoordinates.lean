import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.IntersectionTransport

/-!
# Chamber coordinates of standard intersections

When the source intersection of a Weyl element `w` is the refined Levi of a
refinement `S`, every flattened block of `S` is carried by `w` into one block of
`C`.  Inverse Weyl transport then carries the block scalars of `C` to flattened
block scalars of `S`, and a minimal representative keeps the within-block order.
-/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport

universe uF

variable {n : ℕ}

/-- Entries of a block scalar matrix, by the block of the row coordinate. -/
theorem blockScalar_entry {R : Type uF} [CommRing R] (D : BlockShape n)
    (a : Fin D.length → Rˣ) (x y : Fin n) :
    D.blockScalar R a x y = if x = y then (a (blockIndex D x) : R) else 0 := by
  obtain ⟨i, r, rfl⟩ := TotalConjugatingCount.index_surjective D x
  obtain ⟨j, s, rfl⟩ := TotalConjugatingCount.index_surjective D y
  by_cases hij : i = j
  · subst hij
    rw [D.blockScalar_apply_same, blockIndex_index]
    simp only [(D.index i).injective.eq_iff]
  · rw [D.blockScalar_apply_ne R a r s hij, ite_eq_right (index_ne_of_block_ne D hij r s)]

variable (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)

/-- Coordinates sharing a flattened block of the refinement have images under
`w` in one block of `C`, when the source intersection is the refined Levi. -/
theorem blockIndex_eq_of_sourceLevi_eq {R : Type uF} [CommRing R] [Nontrivial R]
    (hS : sourceLevi R B C w = refinedLevi R B S) {x y : Fin n}
    (h : blockIndex (B.flatten S) x = blockIndex (B.flatten S) y) :
    blockIndex C (w x) = blockIndex C (w y) := by
  obtain ⟨i, a, rfl⟩ := TotalConjugatingCount.index_surjective B x
  have hy : blockIndex B y = i := by
    rw [ProductLeviMinimalIndex.blockIndex_eq_flatten B S y, ← h,
      ← ProductLeviMinimalIndex.blockIndex_eq_flatten, blockIndex_index]
  obtain ⟨b, rfl⟩ := exists_index_of_blockIndex_eq B hy
  rw [ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff] at h
  by_contra hne
  let m : B.Levi R := Pi.mulSingle i (permutation (B.size i) R (Equiv.swap a b))
  have hmi : m i = permutation (B.size i) R (Equiv.swap a b) := Pi.mulSingle_eq_same _ _
  have hm : m ∈ refinedLevi R B S := by
    rw [mem_refinedLevi]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [hmi, CuspidalSupport.levi_mem_iff]
      intro r s hrs
      rw [permutation_entry, ite_eq_right]
      intro hsw
      apply hrs
      rw [← hsw]
      by_cases hsa : s = a
      · rw [hsa, Equiv.swap_apply_left, h]
      · by_cases hsb : s = b
        · rw [hsb, Equiv.swap_apply_right, h]
        · rw [Equiv.swap_apply_of_ne_of_ne hsa hsb]
    · rw [show m j = 1 from Pi.mulSingle_eq_of_ne hj _]
      exact one_mem _
  rw [← hS, mem_sourceLevi_iff] at hm
  have h1 := hm i a b hne
  rw [hmi, permutation_entry, ite_eq_left (Equiv.swap_apply_right a b)] at h1
  exact one_ne_zero h1

/-- The block of `C` containing the image under `w` of the first coordinate of
each flattened block of the refinement. -/
def chamberIndex (k : Fin (B.flatten S).length) : Fin C.length :=
  blockIndex C (w ((B.flatten S).index k ⟨0, (B.flatten S).positive k⟩))

/-- Every coordinate of a flattened block is carried into its chamber block. -/
theorem chamberIndex_blockIndex {R : Type uF} [CommRing R] [Nontrivial R]
    (hS : sourceLevi R B C w = refinedLevi R B S) (x : Fin n) :
    chamberIndex B C w S (blockIndex (B.flatten S) x) = blockIndex C (w x) :=
  blockIndex_eq_of_sourceLevi_eq B C w S hS (blockIndex_index _ _ _)

/-- The chamber block of a nested block, read at any of its coordinates. -/
theorem chamberIndex_flattenBlockEquiv {R : Type uF} [CommRing R] [Nontrivial R]
    (hS : sourceLevi R B C w = refinedLevi R B S) (j : Fin B.length)
    (i : Fin (S j).length) (r : Fin ((S j).size i)) :
    chamberIndex B C w S (B.flattenBlockEquiv S ⟨j, i⟩) =
      blockIndex C (w (B.index j ((S j).index i r))) := by
  rw [← chamberIndex_blockIndex B C w S hS, ProductLeviMinimalIndex.blockIndex_flatten_index,
    blockIndex_index]

/-- For a representative increasing on every block of `B`, the chamber index
is monotone inside every block of `B`. -/
theorem monotone_chamberIndex {R : Type uF} [CommRing R] [Nontrivial R]
    (hS : sourceLevi R B C w = refinedLevi R B S)
    (hw : ∀ i, StrictMono (fun a : Fin (B.size i) => w (B.index i a))) (j : Fin B.length) :
    Monotone fun i : Fin (S j).length => chamberIndex B C w S (B.flattenBlockEquiv S ⟨j, i⟩) := by
  intro i i' hii'
  show chamberIndex B C w S (B.flattenBlockEquiv S ⟨j, i⟩) ≤
    chamberIndex B C w S (B.flattenBlockEquiv S ⟨j, i'⟩)
  rw [chamberIndex_flattenBlockEquiv B C w S hS j i ⟨0, (S j).positive i⟩,
    chamberIndex_flattenBlockEquiv B C w S hS j i' ⟨0, (S j).positive i'⟩]
  apply blockIndex_monotone
  apply (hw j).monotone
  rcases hii'.lt_or_eq with hlt | rfl
  · exact ((S j).index_lt_index_of_block_lt hlt _ _).le
  · exact le_rfl

section BlockScalar

variable (R : Type uF) [CommRing R]

/-- Flattened block scalars, in the actual refined Levi subgroup. -/
def flattenedBlockScalar : (Fin (B.flatten S).length → Rˣ) →* refinedLevi R B S :=
  (flattenedLeviEquiv R B S).toMonoidHom.comp ((B.flatten S).blockScalarLevi R)

@[simp] theorem flattenedBlockScalar_apply (a : Fin (B.flatten S).length → Rˣ) :
    flattenedBlockScalar B S R a = flattenedLeviEquiv R B S ((B.flatten S).blockScalarLevi R a) :=
  rfl

/-- Flattened block scalars are central in the refined Levi. -/
theorem flattenedBlockScalar_commute (a : Fin (B.flatten S).length → Rˣ)
    (g : refinedLevi R B S) : Commute (flattenedBlockScalar B S R a) g := by
  change flattenedLeviEquiv R B S _ * g = g * flattenedLeviEquiv R B S _
  rw [← (flattenedLeviEquiv R B S).apply_symm_apply g, ← map_mul, ← map_mul,
    (B.flatten S).blockScalarLevi_commute]

/-- Restriction of block scalars along the chamber index. -/
def chamberRestriction : (Fin C.length → Rˣ) →* (Fin (B.flatten S).length → Rˣ) where
  toFun a k := a (chamberIndex B C w S k)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem chamberRestriction_apply (a : Fin C.length → Rˣ)
    (k : Fin (B.flatten S).length) :
    chamberRestriction B C w S R a k = a (chamberIndex B C w S k) := rfl

/-- Inverse Weyl transport carries block scalars of `C` to flattened block
scalars of the refinement, read through the chamber index. -/
theorem intersectionLeviConjugation_symm_blockScalar [Nontrivial R]
    (hS : sourceLevi R B C w = refinedLevi R B S)
    (a : Fin C.length → Rˣ) (m : sourceLevi R C B w⁻¹)
    (hm : m.val = C.blockScalarLevi R a) :
    ((intersectionLeviConjugation R B C w).symm m).val =
      (flattenedBlockScalar B S R (chamberRestriction B C w S R a)).val := by
  apply B.leviEmbedding_injective R
  rw [intersectionLeviConjugation_symm_embedding, flattenedBlockScalar_apply,
    flattenedLeviEquiv_embedding, hm]
  have hconj : ∀ g : GeneralLinear n R, (permutation n R w)⁻¹ * g * permutation n R w =
      permutation n R w⁻¹ * g * (permutation n R w⁻¹)⁻¹ := by
    intro g
    rw [map_inv, inv_inv]
  apply Units.ext
  ext x y
  change ((permutation n R w)⁻¹ * C.blockScalar R a * permutation n R w) x y =
    (B.flatten S).blockScalar R (chamberRestriction B C w S R a) x y
  rw [hconj, permutation_conjugate_entry, inv_inv, blockScalar_entry, blockScalar_entry,
    chamberRestriction_apply, chamberIndex_blockIndex B C w S hS]
  simp only [w.injective.eq_iff]

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_flattenedBlockScalar : Continuous (flattenedBlockScalar B S R) :=
  (flattenedLeviEquivContinuous R B S).continuous.comp
    (continuous_pi fun j =>
      (GeneralLinear.scalarContinuous (n := (B.flatten S).size j)).continuous.comp
        (continuous_apply j))

end Topology

end BlockScalar

end Langlands.Geometric
