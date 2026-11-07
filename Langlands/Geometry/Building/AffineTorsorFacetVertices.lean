import Langlands.Geometry.Building.AffineFacetVertexIncidence
import Langlands.Geometry.Building.ValuationBuildingIsoGeometry

/-! # Finite actual facet vertices on affine torsors -/

noncomputable section

universe u v w z

namespace Langlands.Geometry.Building.AffineRootSystem

open Set

section Transport

variable {V : Type u} {A : Type v} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {W : Type w} {C : Type z} [AddCommGroup W] [Module ℝ W] [AddTorsor W C]

/-- Full root transport preserves membership in the original weak-sign closure. -/
theorem mem_facetClosure_transportedRoots_iff (e : A ≃ᵃ[ℝ] C)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (p x : A) :
    e x ∈ facetClosure (transportedRoots e Ψ) (e p) ↔ x ∈ facetClosure Ψ p := by
  rw [← image_facetClosure_transportedRoots]
  exact e.injective.mem_set_image

end Transport

section FiniteVertices

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Finite vertices in an affine torsor, obtained from vector coordinates.
The membership theorem removes all dependence on the chosen coordinate origin. -/
def torsorFacetClosureVertexFinset (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    Finset A :=
  let e : V ≃ᵃ[ℝ] A := AffineEquiv.vaddConst ℝ (Classical.arbitrary A)
  (facetClosureVertexFinset (hΨ.transport e.symm) (e.symm p)).map e.toEquiv.toEmbedding

@[simp] theorem mem_torsorFacetClosureVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p x : A) :
    x ∈ torsorFacetClosureVertexFinset hΨ p ↔
      x ∈ facetClosure Ψ p ∧ IsVertex Ψ x := by
  let e : V ≃ᵃ[ℝ] A := AffineEquiv.vaddConst ℝ (Classical.arbitrary A)
  change x ∈ (facetClosureVertexFinset (hΨ.transport e.symm) (e.symm p)).map
    e.toEquiv.toEmbedding ↔ _
  constructor
  · rintro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    change e y = x at hxy
    subst x
    rw [mem_facetClosureVertexFinset] at hy
    have he : e.symm (e y) = y := e.symm_apply_apply y
    exact ⟨(mem_facetClosure_transportedRoots_iff e.symm Ψ p (e y)).mp
      (he.symm ▸ hy.1),
      (isVertex_transportedRoots_iff e.symm Ψ (e y)).mp (he.symm ▸ hy.2)⟩
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [mem_facetClosureVertexFinset]
    exact ⟨(mem_facetClosure_transportedRoots_iff e.symm Ψ p x).mpr hx.1,
      (isVertex_transportedRoots_iff e.symm Ψ x).mpr hx.2⟩

/-- Corrected affine root systems have nonempty finite vertex sets in every
facet closure, including rank zero. -/
theorem torsorFacetClosureVertexFinset_nonempty
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    (torsorFacetClosureVertexFinset hΨ p).Nonempty := by
  unfold torsorFacetClosureVertexFinset
  exact (facetClosureVertexFinset_nonempty _ _).map

/-- The finite vertex encoding preserves and reflects closed-facet inclusion
on the original affine torsor. -/
theorem torsorFacetClosureVertexFinset_subset_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    torsorFacetClosureVertexFinset hΨ p ⊆ torsorFacetClosureVertexFinset hΨ q ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  let e : V ≃ᵃ[ℝ] A := AffineEquiv.vaddConst ℝ (Classical.arbitrary A)
  change (facetClosureVertexFinset (hΨ.transport e.symm) (e.symm p)).map
      e.toEquiv.toEmbedding ⊆
    (facetClosureVertexFinset (hΨ.transport e.symm) (e.symm q)).map
      e.toEquiv.toEmbedding ↔ _
  rw [Finset.map_subset_map, facetClosureVertexFinset_subset_iff,
    ← image_facetClosure_transportedRoots e.symm Ψ p,
    ← image_facetClosure_transportedRoots e.symm Ψ q]
  exact Set.image_subset_image_iff e.symm.injective

/-- Actual affine face incidence is finite vertex containment. -/
theorem isFaceOf_facet_iff_torsorVertexFinset_subset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    IsFaceOf Ψ (facet Ψ p) (facet Ψ q) ↔
      torsorFacetClosureVertexFinset hΨ p ⊆ torsorFacetClosureVertexFinset hΨ q :=
  isFaceOf_facet_iff_facetClosure_subset.trans
    (torsorFacetClosureVertexFinset_subset_iff hΨ p q).symm

/-- The finite actual vertices determine precisely the original facet class. -/
theorem torsorFacetClosureVertexFinset_eq_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    torsorFacetClosureVertexFinset hΨ p = torsorFacetClosureVertexFinset hΨ q ↔
      facetRel Ψ p q := by
  rw [le_antisymm_iff, torsorFacetClosureVertexFinset_subset_iff,
    torsorFacetClosureVertexFinset_subset_iff, ← le_antisymm_iff]
  exact facetClosure_eq_facetClosure_iff

end FiniteVertices

end Langlands.Geometry.Building.AffineRootSystem
