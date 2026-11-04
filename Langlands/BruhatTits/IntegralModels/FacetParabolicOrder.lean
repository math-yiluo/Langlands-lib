import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.GroupScheme.Rational.MinimalParabolic

/-! # The KP order correspondence for all incident building facets

Facets and incidence use the actual reduced building and translated apartment
charts. The parabolic map uses the actual special-fibre model morphisms.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- All facets of the actual reduced building, including every translated apartment. -/
abbrev BuildingFacet : Type u :=
  {F : Set B.ReducedBuilding // B.IsFacet F}

/-- `F ≺ F'`: in a common translated actual apartment, `F` is a face of `F'`.
The face relation uses the affine-root closure formula, including equality. -/
def FacetPrecedes (F F' : BuildingFacet B) : Prop :=
  ∃ (g : rationalPoints G) (Fa Fa' : Set B.Apartment),
    AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' ∧
      F.val = B.translatedApartmentMap g '' Fa ∧
      F'.val = B.translatedApartmentMap g '' Fa'

/-- All building facets incident above a fixed facet. -/
abbrev IncidentFacets (F : BuildingFacet B) : Type u :=
  {F' : BuildingFacet B // FacetPrecedes B F F'}

/-- Incidence includes each facet itself. This uses only its apartment presentation. -/
theorem facetPrecedes_refl (F : BuildingFacet B) : FacetPrecedes B F F := by
  obtain ⟨g, Fa, ⟨x, rfl⟩, hF⟩ := F.property
  refine ⟨g, _, _, ⟨⟨x, rfl⟩, x, rfl,
    AffineRootSystem.facet_subset_facetClosure _ _⟩, hF, hF⟩

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

/-- Supplied models of all actual building facets, and the actual model morphisms
in the direction prescribed by each incidence. Their generic fibres are identities
and their component restrictions commute by `RelativeComponentModelHom`. -/
structure FacetModelData where
  model : BuildingFacet B → RelativeComponentModelData R K G
  morphism : ∀ (F F' : BuildingFacet B), FacetPrecedes B F F' →
    RelativeComponentModelHom (model F') (model F)

namespace FacetModelData

variable {B R} [IsLocalRing R] (M : FacetModelData B R)
  (F : BuildingFacet B) (Q : SpecialFibreQuotientData (M.model F))

/-- The actual subgroup functor `℘_F(F')`: the all-test image of the
schematic image inclusion in the target's reductive quotient. -/
def incidentParabolicImage (F' : IncidentFacets B F) : SubgroupFunctor Q.quotient :=
  SubgroupFunctor.range
    ((M.morphism F F'.val F'.property).reductiveImageInclusion Q)

/-- KP Axiom 4.1.22(5), with its literal order direction: the actual map from
all incident building facets is bijective onto all ground-field parabolic
subgroup functors, and facet incidence gives opposite subgroup inclusion. -/
def HasFacetParabolicOrderBijection : Prop :=
  Set.BijOn (M.incidentParabolicImage F Q) Set.univ
    {P | IsParabolicFunctor P} ∧
      ∀ F₁ F₂ : IncidentFacets B F, FacetPrecedes B F₁.val F₂.val →
        M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁

variable {M F Q}

/-- Every incident facet has an actual parabolic image. -/
theorem HasFacetParabolicOrderBijection.isParabolic
    (h : M.HasFacetParabolicOrderBijection F Q) (F' : IncidentFacets B F) :
    IsParabolicFunctor (M.incidentParabolicImage F Q F') :=
  h.1.mapsTo (Set.mem_univ F')

/-- Equality of the actual subgroup functors recovers the incident facet. -/
theorem HasFacetParabolicOrderBijection.injective
    (h : M.HasFacetParabolicOrderBijection F Q) :
    Function.Injective (M.incidentParabolicImage F Q) :=
  fun _ _ heq => h.1.injOn (Set.mem_univ _) (Set.mem_univ _) heq

/-- Every actual ground-field parabolic subgroup of the quotient is attained. -/
theorem HasFacetParabolicOrderBijection.surjective
    (h : M.HasFacetParabolicOrderBijection F Q)
    (P : SubgroupFunctor Q.quotient) (hP : IsParabolicFunctor P) :
    ∃ F' : IncidentFacets B F, M.incidentParabolicImage F Q F' = P := by
  obtain ⟨F', _, hF'⟩ := h.1.surjOn hP
  exact ⟨F', hF'⟩

/-- Increasing incident facets give decreasing all-test subgroup functors. -/
theorem HasFacetParabolicOrderBijection.order_preserving
    (h : M.HasFacetParabolicOrderBijection F Q)
    (F₁ F₂ : IncidentFacets B F) (hF : FacetPrecedes B F₁.val F₂.val) :
    M.incidentParabolicImage F Q F₂ ≤ M.incidentParabolicImage F Q F₁ :=
  h.2 F₁ F₂ hF

end FacetModelData
end Langlands.BruhatTits.IntegralModels
