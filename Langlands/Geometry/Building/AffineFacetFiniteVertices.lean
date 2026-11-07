import Langlands.Geometry.Building.AffineFacetVertexGeneration
import Langlands.Geometry.Building.AffineFacetCompactness
import Langlands.Geometry.Building.AffineChamberTransitivity

/-! # Finite actual vertices of compact affine facets -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.AffineRootSystem

open Set GalleryGeometry

section Algebra

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  {Ψ : Set (V →ᵃ[ℝ] ℝ)}

/-- The root hyperplanes through a vertex determine that vertex uniquely. -/
theorem eq_of_isVertex_of_vanishingRoots
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) {x y : V}
    (hx : IsVertex Ψ x) (hy : ∀ ψ ∈ vanishingRoots Ψ x, ψ y = 0) :
    y = x := by
  obtain ⟨ε, hε, hsign⟩ :=
    exists_pos_of_eventually (eventually_sign_smul_vadd hΨ x (y - x))
  have hf : x + ε • (y - x) ∈ facet Ψ x := by
    intro ψ hψ
    by_cases hzero : ψ x = 0
    · have hd : ψ.linear (y - x) = 0 := by
        simpa only [vsub_eq_sub, hzero, hy ψ ⟨hψ, hzero⟩, sub_self]
          using ψ.linearMap_vsub y x
      rw [add_comm, ← vadd_eq_add, apply_smul_vadd, hd, hzero]
      simp
    · simpa only [vadd_eq_add, add_comm] using (hsign ψ hψ hzero).symm
  rw [hx, Set.mem_singleton_iff] at hf
  have hz : ε • (y - x) = 0 :=
    add_left_cancel (show x + ε • (y - x) = x + 0 by simpa using hf)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hε.ne')

/-- Distinct actual vertices have distinct sets of vanishing roots. -/
theorem vanishingRoots_injOn_vertices
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) :
    Set.InjOn (vanishingRoots Ψ) {x | IsVertex Ψ x} := by
  intro x hx y _ hxy
  exact (eq_of_isVertex_of_vanishingRoots hΨ hx
    (fun ψ hψ => (hxy ▸ hψ : ψ ∈ vanishingRoots Ψ y).2)).symm

end Algebra

section Topology

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {Ψ : Set (V →ᵃ[ℝ] ℝ)}

/-- The actual roots whose hyperplanes meet a set. -/
def rootsMeetingSet (Ψ : Set (V →ᵃ[ℝ] ℝ)) (C : Set V) :
    Set (V →ᵃ[ℝ] ℝ) :=
  {ψ | ψ ∈ Ψ ∧ ∃ x ∈ C, ψ x = 0}

/-- Bounded root values imply that only finitely many root hyperplanes meet
a compact set. -/
theorem finite_rootsMeetingSet
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {C : Set V} (hC : IsCompact C) : (rootsMeetingSet Ψ C).Finite := by
  choose M hM using fun a : Module.Dual ℝ V =>
    hC.exists_bound_of_continuousOn a.continuous_of_finiteDimensional.continuousOn
  refine (hΨ.finite_bounded_at 0 M).subset ?_
  rintro ψ ⟨hψ, x, hx, hzero⟩
  refine ⟨hψ, ?_⟩
  have he : ψ.linear x = -ψ 0 := by
    simpa only [vsub_eq_sub, sub_zero, hzero, zero_sub] using ψ.linearMap_vsub x 0
  simpa only [Real.norm_eq_abs, he, abs_neg] using hM ψ.linear x hx

/-- A compact set contains finitely many actual zero-dimensional facets. -/
theorem finite_vertices_in_compact
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {C : Set V} (hC : IsCompact C) : {x | x ∈ C ∧ IsVertex Ψ x}.Finite := by
  apply Set.Finite.of_injOn (f := vanishingRoots Ψ)
    (t := Set.powerset (rootsMeetingSet Ψ C)) ?_ ?_
    (finite_rootsMeetingSet hΨ hC).powerset
  · intro x hx ψ hψ
    exact ⟨hψ.1, x, hx.1, hψ.2⟩
  · exact (vanishingRoots_injOn_vertices hΨ).mono fun _ h => h.2

/-- In particular a compact facet closure has finitely many incident vertices. -/
theorem finite_facetClosureVertices
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p : V)
    (hc : IsCompact (facetClosure Ψ p)) : (facetClosureVertices Ψ p).Finite :=
  finite_vertices_in_compact hΨ hc

/-- A compact convex facet closure is the convex hull of its finitely many
actual vertices; no closure operation is needed. -/
theorem convexHull_facetClosureVertices
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p : V)
    (hc : IsCompact (facetClosure Ψ p)) (hv : Convex ℝ (facetClosure Ψ p)) :
    convexHull ℝ (facetClosureVertices Ψ p) = facetClosure Ψ p := by
  rw [← closure_convexHull_facetClosureVertices hΨ p hc hv,
    ((finite_facetClosureVertices hΨ p hc).isClosed_convexHull ℝ).closure_eq]

/-- Every compact convex facet closure contains an actual vertex. -/
theorem nonempty_facetClosureVertices
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (p : V)
    (hc : IsCompact (facetClosure Ψ p)) (hv : Convex ℝ (facetClosure Ψ p)) :
    (facetClosureVertices Ψ p).Nonempty := by
  by_contra h
  have he := convexHull_facetClosureVertices hΨ p hc hv
  rw [Set.not_nonempty_iff_eq_empty.mp h, convexHull_empty] at he
  exact Set.not_nonempty_empty ⟨p, he.symm ▸ mem_facetClosure_self Ψ p⟩

/-- The finite vertex set of a facet in a corrected affine root system. -/
def facetClosureVertexFinset (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    Finset V :=
  (finite_facetClosureVertices hΨ.isLocallyFiniteReflectionArrangement p
    (hΨ.isCompact_facetClosure p)).toFinset

@[simp] theorem mem_facetClosureVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : V) :
    q ∈ facetClosureVertexFinset hΨ p ↔
      q ∈ facetClosure Ψ p ∧ IsVertex Ψ q := by
  unfold facetClosureVertexFinset
  exact Set.Finite.mem_toFinset _

theorem facetClosureVertexFinset_nonempty
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    (facetClosureVertexFinset hΨ p).Nonempty := by
  obtain ⟨q, hq⟩ := nonempty_facetClosureVertices
    hΨ.isLocallyFiniteReflectionArrangement p (hΨ.isCompact_facetClosure p)
    (convex_facetClosure Ψ p)
  exact ⟨q, (mem_facetClosureVertexFinset hΨ p q).mpr hq⟩

theorem convexHull_facetClosureVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : V) :
    convexHull ℝ (↑(facetClosureVertexFinset hΨ p) : Set V) = facetClosure Ψ p := by
  have he : (↑(facetClosureVertexFinset hΨ p) : Set V) = facetClosureVertices Ψ p := by
    ext q
    exact mem_facetClosureVertexFinset hΨ p q
  rw [he]
  exact convexHull_facetClosureVertices hΨ.isLocallyFiniteReflectionArrangement p
    (hΨ.isCompact_facetClosure p) (convex_facetClosure Ψ p)

end Topology

end Langlands.Geometry.Building.AffineRootSystem
