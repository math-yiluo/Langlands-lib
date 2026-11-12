import Langlands.Geometry.Building.AffineFacetCentroids

/-! # Intersections of original closed affine facets -/

noncomputable section

universe u v w z

namespace Langlands.Geometry.Building.AffineRootSystem

open Set

section Intersections

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

local instance instDecidableEq_affineFacetIntersections : DecidableEq A := Classical.decEq _

/-- Two original closed facets meet exactly when they share an actual vertex. -/
theorem facetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty ↔
      (torsorFacetClosureVertexFinset hΨ p ∩
        torsorFacetClosureVertexFinset hΨ q).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hxp, hxq⟩
    obtain ⟨v, hv⟩ := torsorFacetClosureVertexFinset_nonempty hΨ x
    obtain ⟨hvx, hv⟩ := (mem_torsorFacetClosureVertexFinset hΨ x v).mp hv
    exact ⟨v, Finset.mem_inter.mpr
      ⟨(mem_torsorFacetClosureVertexFinset hΨ p v).mpr
        ⟨mem_facetClosure_trans hxp hvx, hv⟩,
      (mem_torsorFacetClosureVertexFinset hΨ q v).mpr
        ⟨mem_facetClosure_trans hxq hvx, hv⟩⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨hvp, hvq⟩ := Finset.mem_inter.mp hv
    exact ⟨v, ((mem_torsorFacetClosureVertexFinset hΨ p v).mp hvp).1,
      ((mem_torsorFacetClosureVertexFinset hΨ q v).mp hvq).1⟩

/-- The centroid of the common actual vertices. The geometric conclusions below
apply when the two original closed facets have nonempty intersection. -/
def facetIntersectionCentroid (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) : A := by
  classical
  exact (torsorFacetClosureVertexFinset hΨ p ∩
    torsorFacetClosureVertexFinset hΨ q).centroid ℝ id

/-- Every nonempty intersection is precisely the original closed facet of the
centroid of its common actual vertices. -/
theorem facetClosure_facetIntersectionCentroid
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A)
    (hpq : (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty) :
    facetClosure Ψ (facetIntersectionCentroid hΨ p q) =
      facetClosure Ψ p ∩ facetClosure Ψ q := by
  classical
  let s := torsorFacetClosureVertexFinset hΨ p ∩ torsorFacetClosureVertexFinset hΨ q
  have hs : s.Nonempty :=
    (facetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty hΨ p q).mp hpq
  have hsp : ∀ v ∈ s, v ∈ facetClosure Ψ p :=
    fun v hv => ((mem_torsorFacetClosureVertexFinset hΨ p v).mp
      (Finset.mem_inter.mp hv).1).1
  have hsq : ∀ v ∈ s, v ∈ facetClosure Ψ q :=
    fun v hv => ((mem_torsorFacetClosureVertexFinset hΨ q v).mp
      (Finset.mem_inter.mp hv).2).1
  change facetClosure Ψ (s.centroid ℝ id) = _
  apply Set.Subset.antisymm
  · exact Set.subset_inter
      (facetClosure_subset_facetClosure_iff.mpr (centroid_mem_facetClosure s hs hsp))
      (facetClosure_subset_facetClosure_iff.mpr (centroid_mem_facetClosure s hs hsq))
  · intro x hx
    have hxc : facetClosure Ψ x ⊆ facetClosure Ψ (s.centroid ℝ id) := by
      apply (torsorFacetClosureVertexFinset_subset_iff hΨ x _).mp
      intro v hv
      obtain ⟨hvx, hv⟩ := (mem_torsorFacetClosureVertexFinset hΨ x v).mp hv
      have hvs : v ∈ s := Finset.mem_inter.mpr
        ⟨(mem_torsorFacetClosureVertexFinset hΨ p v).mpr
          ⟨mem_facetClosure_trans hx.1 hvx, hv⟩,
        (mem_torsorFacetClosureVertexFinset hΨ q v).mpr
          ⟨mem_facetClosure_trans hx.2 hvx, hv⟩⟩
      exact (mem_torsorFacetClosureVertexFinset hΨ _ v).mpr
        ⟨mem_facetClosure_centroid s hs hsp v hvs, hv⟩
    exact hxc (mem_facetClosure_self Ψ x)

/-- The actual vertices of a nonempty intersection are exactly the common
actual vertices of the two closed facets. -/
theorem vertexFinset_facetIntersectionCentroid
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A)
    (hpq : (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty) :
    torsorFacetClosureVertexFinset hΨ (facetIntersectionCentroid hΨ p q) =
      torsorFacetClosureVertexFinset hΨ p ∩ torsorFacetClosureVertexFinset hΨ q := by
  classical
  ext v
  simp only [mem_torsorFacetClosureVertexFinset, Finset.mem_inter,
    facetClosure_facetIntersectionCentroid hΨ p q hpq, Set.mem_inter_iff]
  tauto

/-- The intersection representative is already the canonical centroid of its
own original facet. -/
theorem facetCentroid_facetIntersectionCentroid
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A)
    (hpq : (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty) :
    facetCentroid hΨ (facetIntersectionCentroid hΨ p q) =
      facetIntersectionCentroid hΨ p q := by
  unfold facetCentroid
  rw [vertexFinset_facetIntersectionCentroid hΨ p q hpq]
  rfl

/-- Nonempty intersections of original closed facets remain original closed facets. -/
theorem exists_facetClosure_eq_inter (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A)
    (hpq : (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty) :
    ∃ r : A, facetClosure Ψ r = facetClosure Ψ p ∩ facetClosure Ψ q :=
  ⟨facetIntersectionCentroid hΨ p q, facetClosure_facetIntersectionCentroid hΨ p q hpq⟩

/-- The representative is symmetric in the two facets. -/
theorem facetIntersectionCentroid_comm (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    facetIntersectionCentroid hΨ p q = facetIntersectionCentroid hΨ q p := by
  classical
  unfold facetIntersectionCentroid
  rw [Finset.inter_comm]

/-- The representative depends only on the two original facet classes. -/
theorem facetIntersectionCentroid_eq_of_facetRel
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {p p' q q' : A}
    (hp : facetRel Ψ p p') (hq : facetRel Ψ q q') :
    facetIntersectionCentroid hΨ p q = facetIntersectionCentroid hΨ p' q' := by
  classical
  unfold facetIntersectionCentroid
  rw [(torsorFacetClosureVertexFinset_eq_iff hΨ p p').mpr hp,
    (torsorFacetClosureVertexFinset_eq_iff hΨ q q').mpr hq]

end Intersections

section Transport

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {W : Type w} {C : Type z}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [AddTorsor W C]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The centroid representative of a nonempty closed-facet intersection
commutes with full affine root transport. -/
theorem facetIntersectionCentroid_transportedRoots
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] C) (p q : A)
    (hpq : (facetClosure Ψ p ∩ facetClosure Ψ q).Nonempty) :
    facetIntersectionCentroid (hΨ.transport e) (e p) (e q) =
      e (facetIntersectionCentroid hΨ p q) := by
  classical
  unfold facetIntersectionCentroid
  rw [torsorFacetClosureVertexFinset_transportedRoots,
    torsorFacetClosureVertexFinset_transportedRoots, ← Finset.map_inter]
  exact (affineEquiv_centroid_map e _
    ((facetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty hΨ p q).mp hpq)).symm

end Transport

end Langlands.Geometry.Building.AffineRootSystem
