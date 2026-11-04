import Langlands.AlgebraicGeometry.OpenCoverDimension

/-! # Dimension of open intersections with irreducible components -/

universe u v

open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X : Type u} [TopologicalSpace X]

/-- The same actual intersection, viewed in either order as a subspace. -/
def subtypePreimageCommHomeomorph (S T : Set X) :
    ((Subtype.val : S → X) ⁻¹' T) ≃ₜ ((Subtype.val : T → X) ⁻¹' S) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- An open of an actual subspace is obtained by pulling back the ambient open. -/
def openInSubspace (S : Set X) (U : Opens X) : Opens S :=
  ⟨(Subtype.val : S → X) ⁻¹' U, U.isOpen.preimage continuous_subtype_val⟩

/-- A component of an open subspace extends to the closure of its actual image. -/
theorem closure_image_mem_irreducibleComponents_open
    (U : Opens X) (Z : Set U) (hZ : Z ∈ irreducibleComponents U) :
    closure ((Subtype.val : U → X) '' Z) ∈ irreducibleComponents X := by
  obtain ⟨T, hT, hZT⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ((Subtype.val : U → X) '' Z) (hZ.1.image _ continuous_subtype_val.continuousOn)
  have hpre : Z ⊆ (Subtype.val : U → X) ⁻¹' T := image_subset_iff.mp hZT
  have hne : (T ∩ range (Subtype.val : U → X)).Nonempty := by
    obtain ⟨x, hx⟩ := hZ.1.nonempty
    exact ⟨x, hpre hx, ⟨x, rfl⟩⟩
  have hp := preimage_mem_irreducibleComponents hT U.isOpenEmbedding' hne
  have heq : (Subtype.val : U → X) ⁻¹' T = Z :=
    subset_antisymm (hZ.2 hp.1 hpre) hpre
  have hc := closure_image_preimage_of_isPreirreducible
    (Subtype.val : U → X) U.isOpenEmbedding'.isOpenMap T
    (by simpa [heq] using hZ.1.nonempty) hT.1.2
    (isClosed_of_mem_irreducibleComponents T hT)
  rw [heq] at hc
  exact hc ▸ hT

/-- Restricting the ambient closure recovers the original component exactly. -/
theorem preimage_closure_image_irreducibleComponent_open
    (U : Opens X) (Z : Set U) (hZ : Z ∈ irreducibleComponents U) :
    (Subtype.val : U → X) ⁻¹' closure ((Subtype.val : U → X) '' Z) = Z := by
  rw [U.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val, preimage_image_eq _ Subtype.val_injective]
  exact (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq

/-- Constancy of dimension on nonempty opens can be checked on an open cover
of a preirreducible space. Empty members of the cover are allowed. -/
theorem topologicalKrullDim_open_eq_of_openCover [PreirreducibleSpace X]
    {ι : Type v} (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hdim : ∀ i (W : Opens (U i)), (W : Set (U i)).Nonempty →
      topologicalKrullDim W = topologicalKrullDim (U i))
    (V : Opens X) (hV : (V : Set X).Nonempty) :
    topologicalKrullDim V = topologicalKrullDim X := by
  apply le_antisymm (topologicalKrullDim_subspace_le X V)
  rw [topologicalKrullDim_eq_iSup_openCover U hcover]
  refine iSup_le fun i => ?_
  by_cases hi : (U i : Set X).Nonempty
  · let W := openInSubspace (U i : Set X) V
    have hW : (W : Set (U i)).Nonempty := by
      obtain ⟨x, hxi, hxV⟩ :=
        nonempty_preirreducible_inter (U i).isOpen V.isOpen hi hV
      exact ⟨⟨x, hxi⟩, hxV⟩
    rw [← hdim i W hW]
    exact ((subtypePreimageCommHomeomorph (U i : Set X) V).isHomeomorph.topologicalKrullDim_eq _).trans_le (topologicalKrullDim_subspace_le V _)
  · exact (Topology.IsEmbedding.inclusion
      (show (U i : Set X) ⊆ V from fun x hx => (hi ⟨x, hx⟩).elim)).isInducing.topologicalKrullDim_le

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
