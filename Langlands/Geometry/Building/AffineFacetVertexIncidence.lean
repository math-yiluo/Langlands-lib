import Langlands.Geometry.Building.AffineFacetFiniteVertices
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Hom.Basic

/-! # Actual affine face incidence in finite vertex coordinates -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

open Set

section Algebra

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {p q : A}

/-- Containment of closed facets is the existing pointwise incidence relation. -/
theorem facetClosure_subset_facetClosure_iff :
    facetClosure Ψ p ⊆ facetClosure Ψ q ↔ p ∈ facetClosure Ψ q :=
  ⟨fun h => h (mem_facetClosure_self Ψ p),
    fun h _ hx => mem_facetClosure_trans h hx⟩

/-- Closed facets determine the original open facets. -/
theorem facetClosure_eq_facetClosure_iff :
    facetClosure Ψ p = facetClosure Ψ q ↔ facetRel Ψ p q := by
  refine ⟨fun h ψ hψ => ?_, facetClosure_eq_of_facetRel⟩
  have hp := (facetClosure_subset_facetClosure_iff.mp h.subset) ψ hψ
  have hq := (facetClosure_subset_facetClosure_iff.mp h.symm.subset) ψ hψ
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact hp.trans hq.symm
    · exact hq.symm
  · exact hp

/-- The original affine face predicate is exactly closed-facet containment. -/
theorem isFaceOf_facet_iff_facetClosure_subset :
    IsFaceOf Ψ (facet Ψ p) (facet Ψ q) ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  rw [facetClosure_subset_facetClosure_iff]
  constructor
  · rintro ⟨_, r, hr, hpr⟩
    have he := facetClosure_eq_of_facetRel (facet_eq_facet_iff.mp hr)
    rw [← he]
    exact hpr (mem_facet_self Ψ p)
  · intro h
    exact ⟨isFacet_facet Ψ p, q, rfl, facet_subset_facetClosure_iff.mpr h⟩

end Algebra

section Topology

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Ψ : Set (V →ᵃ[ℝ] ℝ)}

/-- Convex generation identifies closed-facet containment with containment of
the actual incident vertex sets. -/
theorem facetClosureVertices_subset_iff
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p q : V)
    (hp : IsCompact (facetClosure Ψ p)) (hq : IsCompact (facetClosure Ψ q))
    (hvp : Convex ℝ (facetClosure Ψ p)) (hvq : Convex ℝ (facetClosure Ψ q)) :
    facetClosureVertices Ψ p ⊆ facetClosureVertices Ψ q ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  constructor
  · intro h
    rw [← convexHull_facetClosureVertices hΨ p hp hvp,
      ← convexHull_facetClosureVertices hΨ q hq hvq]
    exact convexHull_mono h
  · exact fun h _ hx => ⟨h hx.1, hx.2⟩

/-- For a corrected affine root system, finite vertex containment is incidence. -/
theorem facetClosureVertexFinset_subset_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    facetClosureVertexFinset hΨ p ⊆ facetClosureVertexFinset hΨ q ↔
      facetClosure Ψ p ⊆ facetClosure Ψ q := by
  have he :
      facetClosureVertexFinset hΨ p ⊆ facetClosureVertexFinset hΨ q ↔
        facetClosureVertices Ψ p ⊆ facetClosureVertices Ψ q := by
    simp only [Finset.subset_iff, mem_facetClosureVertexFinset]
    rfl
  rw [he]
  exact facetClosureVertices_subset_iff hΨ.isLocallyFiniteReflectionArrangement p q
    (hΨ.isCompact_facetClosure p) (hΨ.isCompact_facetClosure q)
    (convex_facetClosure Ψ p) (convex_facetClosure Ψ q)

/-- Finite vertex sets agree precisely on the original facet classes. -/
theorem facetClosureVertexFinset_eq_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    facetClosureVertexFinset hΨ p = facetClosureVertexFinset hΨ q ↔
      facetRel Ψ p q := by
  rw [le_antisymm_iff, facetClosureVertexFinset_subset_iff,
    facetClosureVertexFinset_subset_iff,
    ← le_antisymm_iff]
  exact facetClosure_eq_facetClosure_iff

/-- The finite encoding preserves the actual affine face relation. -/
theorem isFaceOf_facet_iff_vertexFinset_subset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    IsFaceOf Ψ (facet Ψ p) (facet Ψ q) ↔
      facetClosureVertexFinset hΨ p ⊆ facetClosureVertexFinset hΨ q :=
  isFaceOf_facet_iff_facetClosure_subset.trans
    (facetClosureVertexFinset_subset_iff hΨ p q).symm

/-- The finite actual vertex coordinates of an original closed facet. -/
def closedFacetVertexFinset (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C : Set.range (facetClosure Ψ)) : Finset V :=
  facetClosureVertexFinset hΨ C.property.choose

@[simp] theorem mem_closedFacetVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C : Set.range (facetClosure Ψ)) (x : V) :
    x ∈ closedFacetVertexFinset hΨ C ↔ x ∈ C.val ∧ IsVertex Ψ x := by
  unfold closedFacetVertexFinset
  rw [mem_facetClosureVertexFinset, C.property.choose_spec]

theorem closedFacetVertexFinset_subset_iff
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (C D : Set.range (facetClosure Ψ)) :
    closedFacetVertexFinset hΨ C ⊆ closedFacetVertexFinset hΨ D ↔ C ≤ D := by
  unfold closedFacetVertexFinset
  rw [facetClosureVertexFinset_subset_iff,
    C.property.choose_spec, D.property.choose_spec]
  rfl

/-- Closed facets, ordered by inclusion, embed into their finite actual vertex
sets, also ordered by inclusion. -/
def closedFacetVertexOrderEmbedding (hΨ : IsAffineRootSystemWithRankZero Ψ) :
    Set.range (facetClosure Ψ) ↪o Finset V :=
  OrderEmbedding.ofMapLEIff (closedFacetVertexFinset hΨ)
    (closedFacetVertexFinset_subset_iff hΨ)

/-- Every original affine facet has only finitely many incident closed faces. -/
theorem finite_closedFacets_below
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    {C : Set.range (facetClosure Ψ) | C.val ⊆ facetClosure Ψ p}.Finite := by
  apply Set.Finite.of_injOn (f := closedFacetVertexFinset hΨ)
    (t := ↑(facetClosureVertexFinset hΨ p).powerset) ?_ ?_
    (facetClosureVertexFinset hΨ p).powerset.finite_toSet
  · intro C hC
    apply Finset.mem_powerset.mpr
    change C.val ⊆ facetClosure Ψ p at hC
    rw [← C.property.choose_spec] at hC
    exact (facetClosureVertexFinset_subset_iff hΨ _ _).mpr hC
  · exact (closedFacetVertexOrderEmbedding hΨ).injective.injOn

end Topology

end Langlands.Geometry.Building.AffineRootSystem
