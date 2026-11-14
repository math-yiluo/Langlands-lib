import Langlands.Geometry.Building.ApartmentFacetClosureFixing
import Langlands.Geometry.Building.IntegerBuildingFacetPartition
import Langlands.Geometry.Building.BoundedRootFixerFiltration

/-! # Positive root filtrations of incident facets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)

include hAS4

/-- The nonstrict root fixer decreases, and the strict root fixer increases,
from a face to an incident facet. -/
theorem rootFixer_comparison_of_incidentFacets {F C : Set D.Apartment}
    (hC : AffineRootSystem.IsFacet D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    {x : D.Apartment} (hx : x ∈ C) (a : relativeRoots i) :
    D.rootFixerPlus a F ≤ D.rootFixerPlus a C ∧
      D.rootFixer a C ≤ D.rootFixer a F := by
  obtain ⟨y, hy⟩ : F.Nonempty := by
    obtain ⟨y, hy⟩ := hFC.1
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
  obtain ⟨hF0, hFp⟩ := D.rootFixer_eq_filtration_of_isFacet hAS4 hFC.1 hy a.2
  obtain ⟨hC0, hCp⟩ := D.rootFixer_eq_filtration_of_isFacet hAS4 hC hx a.2
  have hc := D.filtration_comparison_of_mem_facetClosure hAS4
    (D.mem_facetClosure_of_isFaceOf hFC hx hy) a.2
  rw [hF0, hFp, hC0, hCp]
  exact hc

/-- A root nonnegative on the displacement from a face point to an incident
facet point has the same nonstrict fixer on both facets. -/
theorem rootFixer_eq_of_incidentFacets_of_nonneg {F C : Set D.Apartment}
    (hC : AffineRootSystem.IsFacet D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    {x y : D.Apartment} (hx : x ∈ C) (hy : y ∈ F) (a : relativeRoots i)
    (ha : 0 ≤ rootForm i a (x -ᵥ y)) :
    D.rootFixer a F = D.rootFixer a C := by
  apply le_antisymm
  · rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hFC.1 hy a.2).1,
      (D.rootFixer_eq_filtration_of_isFacet hAS4 hC hx a.2).1]
    have hshift := D.filtration_vadd y (x -ᵥ y) a 0
    rw [vsub_vadd] at hshift
    rw [hshift]
    exact D.filtration_antitone y a (by linarith)
  · exact (D.rootFixer_comparison_of_incidentFacets hAS4 hC hFC hx a).2

/-- Connected reductivity supplies one generic positive system for which
every positive root has equal nonstrict fixers on the two incident facets. -/
theorem exists_genericCocharacter_rootFixer_eq_of_incidentFacets
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {F C : Set D.Apartment}
    (hC : AffineRootSystem.IsFacet D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C) :
    ∃ ν : cocharacterLattice S, IsGenericCocharacter i ν ∧
      ∀ a : relativeRoots i, 0 < latticePairing S a ν →
        D.rootFixer a F = D.rootFixer a C := by
  obtain ⟨x, hx⟩ : C.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨x, hx ▸ AffineRootSystem.mem_facet_self D.affineRoots x⟩
  obtain ⟨y, hy⟩ : F.Nonempty := by
    obtain ⟨y, hy⟩ := hFC.1
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
  obtain ⟨w, hw⟩ := D.exists_mk_vadd_eq y x
  obtain ⟨ν, hν, hadapt⟩ :=
    exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus hG hi w
  refine ⟨ν, hν, fun a ha => ?_⟩
  apply D.rootFixer_eq_of_incidentFacets_of_nonneg hAS4 hC hFC hx hy a
  rw [hw, vadd_vsub, rootForm_mk]
  exact hadapt a a.2 ha

/-- At any reference point, bounded incident facets have equal actual
filtration subgroups at their root-fixer depths for all roots positive on
one generic cocharacter. No equality of the real depths is asserted. -/
theorem exists_genericCocharacter_filtrationDepth_eq_of_incidentFacets
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {F C : Set D.Apartment}
    (hC : AffineRootSystem.IsFacet D.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf D.affineRoots F C)
    (hFb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' F))
    (hCb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' C))
    (z : D.Apartment) :
    ∃ ν : cocharacterLattice S, IsGenericCocharacter i ν ∧
      ∀ a : relativeRoots i, 0 < latticePairing S a ν →
        D.filtration z a (D.rootFixerDepth a z F) =
          D.filtration z a (D.rootFixerDepth a z C) := by
  obtain ⟨ν, hν, heq⟩ :=
    D.exists_genericCocharacter_rootFixer_eq_of_incidentFacets hAS4 hG hi hC hFC
  obtain ⟨x, hx⟩ : C.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨x, hx ▸ AffineRootSystem.mem_facet_self D.affineRoots x⟩
  obtain ⟨y, hy⟩ : F.Nonempty := by
    obtain ⟨y, hy⟩ := hFC.1
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self D.affineRoots y⟩
  refine ⟨ν, hν, fun a ha => ?_⟩
  rw [← D.rootFixer_eq_filtration_of_bounded a z ⟨y, hy⟩ hFb,
    ← D.rootFixer_eq_filtration_of_bounded a z ⟨x, hx⟩ hCb]
  exact heq a ha

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- The actual integer-valued building data supply AS4, connected reductivity,
and maximal splitness for the incident-facet positive-root comparison. -/
theorem exists_genericCocharacter_rootFixer_eq_of_incidentFacets
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C) :
    ∃ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν ∧
      ∀ a : relativeRoots B.i, 0 < latticePairing B.S a ν →
        B.apartment.rootFixer a F = B.apartment.rootFixer a C :=
  B.apartment.exists_genericCocharacter_rootFixer_eq_of_incidentFacets
    B.affineRoot_mem_or_two_smul_mem B.isConnectedReductive B.isMaximalSplitTorus hC hFC

/-- The same unconditional specialization, expressed at the actual bounded
root-fixer depths used by root-filtration models. -/
theorem exists_genericCocharacter_filtrationDepth_eq_of_incidentFacets
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C)
    (hFb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' F))
    (hCb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' C))
    (z : B.Apartment) :
    ∃ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν ∧
      ∀ a : relativeRoots B.i, 0 < latticePairing B.S a ν →
        B.apartment.filtration z a (B.apartment.rootFixerDepth a z F) =
          B.apartment.filtration z a (B.apartment.rootFixerDepth a z C) :=
  B.apartment.exists_genericCocharacter_filtrationDepth_eq_of_incidentFacets
    B.affineRoot_mem_or_two_smul_mem B.isConnectedReductive B.isMaximalSplitTorus
    hC hFC hFb hCb z

/-- A chosen generic cocharacter whose positive roots have equal nonstrict
fixers on the two incident facets. -/
def incidentFacetCocharacter
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C) :
    cocharacterLattice B.S :=
  Classical.choose (B.exists_genericCocharacter_rootFixer_eq_of_incidentFacets hC hFC)

theorem incidentFacetCocharacter_isGeneric
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C) :
    IsGenericCocharacter B.i (B.incidentFacetCocharacter hC hFC) :=
  (Classical.choose_spec
    (B.exists_genericCocharacter_rootFixer_eq_of_incidentFacets hC hFC)).1

theorem rootFixer_eq_of_incidentFacetCocharacter_pos
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C)
    (a : relativeRoots B.i)
    (ha : 0 < latticePairing B.S a (B.incidentFacetCocharacter hC hFC)) :
    B.apartment.rootFixer a F = B.apartment.rootFixer a C :=
  (Classical.choose_spec
    (B.exists_genericCocharacter_rootFixer_eq_of_incidentFacets hC hFC)).2 a ha

/-- The chosen cocharacter works simultaneously at every reference point
and at the actual root-fixer depths of any bounded incident facets. -/
theorem filtrationDepth_eq_of_incidentFacetCocharacter_pos
    {F C : Set B.Apartment}
    (hC : AffineRootSystem.IsFacet B.affineRoots C)
    (hFC : AffineRootSystem.IsFaceOf B.affineRoots F C)
    (hFb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' F))
    (hCb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' C))
    (z : B.Apartment) (a : relativeRoots B.i)
    (ha : 0 < latticePairing B.S a (B.incidentFacetCocharacter hC hFC)) :
    B.apartment.filtration z a (B.apartment.rootFixerDepth a z F) =
      B.apartment.filtration z a (B.apartment.rootFixerDepth a z C) := by
  obtain ⟨x, hx⟩ : C.Nonempty := by
    obtain ⟨x, hx⟩ := hC
    exact ⟨x, hx ▸ AffineRootSystem.mem_facet_self B.affineRoots x⟩
  obtain ⟨y, hy⟩ : F.Nonempty := by
    obtain ⟨y, hy⟩ := hFC.1
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self B.affineRoots y⟩
  rw [← B.apartment.rootFixer_eq_filtration_of_bounded a z ⟨y, hy⟩ hFb,
    ← B.apartment.rootFixer_eq_filtration_of_bounded a z ⟨x, hx⟩ hCb]
  exact B.rootFixer_eq_of_incidentFacetCocharacter_pos hC hFC a ha

end IntegerValuationBuildingData

end Langlands.Geometry.Building
