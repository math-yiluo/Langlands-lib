import Langlands.Geometry.Building.ValuationBuildingFacetIncidenceEmbedding
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # Facet incidence descent for a supplied semilinear action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.MaximalUnramified.SemilinearApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {C : BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : SemilinearApartmentData C)

/-- The fixed subset for this supplied semilinear action. -/
def fixedLocus : Set C.ReducedBuilding :=
  {y | ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y}

/-- Retain the full upstairs facet together with a fixed point in it. -/
abbrev FixedFacet : Type u :=
  {Fd : C.BuildingFacet // (Fd.val ∩ A.fixedLocus).Nonempty}

/-- The part of a full upstairs facet lying in the supplied fixed subset. -/
def fixedFacetPart (Fd : A.FixedFacet) : Set C.ReducedBuilding :=
  Fd.val.val ∩ A.fixedLocus

/-- All full facets meeting the fixed set and incident above a chosen one. -/
abbrev IncidentFixedFacets (Fc : A.FixedFacet) : Type u :=
  {Fd : A.FixedFacet // C.FacetPrecedes Fc.val Fd.val}

variable (B : ValuationBuildingData G)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (hfixed : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (z : B.ReducedBuilding), A.action σ (e z) = e z)
  (hsurj : ∀ y : C.ReducedBuilding,
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y) →
      ∃ z : B.ReducedBuilding, e z = y)

include hfixed hsurj

/-- The two supplied fixed-point hypotheses identify the point-map image
with the fixed locus for the same action. -/
theorem range_eq_fixedLocus : Set.range e = A.fixedLocus := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩ σ
    exact hfixed σ z
  · exact hsurj y

variable (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (hapt : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
  (hfacet : ∀ w : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
      AffineRootSystem.facet B.affineRoots w)
  (hD : B.SatisfiesApartmentAxioms) (hcommon : B.HasCommonApartments)

/-- Source facets correspond to full upstairs facets meeting this supplied
action's fixed locus, with their original incidence relations. -/
def fixedFacetOrderIso :
    @OrderIso (BuildingFacet B) A.FixedFacet
      (B.buildingFacetPartialOrder hD
        (B.apartment.apartmentMap_injective B.isConnectedReductive
          B.isMaximalSplitTorus)).toLE
      ⟨fun Fc Fd => C.FacetPrecedes Fc.val Fd.val⟩ where
  toEquiv :=
    (B.facetRangeEquiv C (rationalExtend F (inertiaFixedField F) G)
      e a hequiv hapt hfacet hD hcommon).trans
        (Equiv.subtypeEquivRight fun Fd => by
          rw [range_eq_fixedLocus A B e hfixed hsurj])
  map_rel_iff' := by
    intro Fc Fd
    exact B.facetPrecedes_facetLift_iff C
      (rationalExtend F (inertiaFixedField F) G)
      e a hequiv hapt hfacet hD hcommon Fc Fd

@[simp] theorem fixedFacetOrderIso_val (Fc : BuildingFacet B) :
    (fixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet hD hcommon Fc).val =
      B.facetLift C e Fc := rfl

/-- The image of a source facet is exactly the fixed part of its full lift. -/
theorem image_eq_fixedFacetPart (Fc : BuildingFacet B) :
    e '' Fc.val =
      A.fixedFacetPart
        (fixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet hD hcommon Fc) := by
  rw [B.image_facetLift C (rationalExtend F (inertiaFixedField F) G)
    e a hequiv hapt hfacet hD hcommon,
    range_eq_fixedLocus A B e hfixed hsurj]
  rfl

/-- The closed source facet likewise gives exactly the fixed part of its
full upstairs combinatorial closure. -/
theorem image_closure_eq_inter_fixedLocus (Fc : BuildingFacet B) :
    e '' B.buildingFacetClosure Fc =
      C.buildingFacetClosure
        (fixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet hD hcommon Fc).val ∩
          A.fixedLocus := by
  rw [B.image_buildingFacetClosure_facetLift C
    (rationalExtend F (inertiaFixedField F) G)
    e a hequiv hapt hfacet hD hcommon,
    range_eq_fixedLocus A B e hfixed hsurj]
  rfl

/-- Restricting the facet correspondence to incident facets retains
preservation and reflection of incidence. -/
def incidentFixedFacetOrderIso (Fc : BuildingFacet B) :
    @OrderIso (IncidentFacets B Fc)
      (A.IncidentFixedFacets
        (fixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet hD hcommon Fc))
      ⟨fun Fd Fe => FacetPrecedes B Fd.val Fe.val⟩
      ⟨fun Fd Fe => C.FacetPrecedes Fd.val.val Fe.val.val⟩ where
  toEquiv :=
    (fixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet hD hcommon).toEquiv.subtypeEquiv
      (fun Fd => (B.facetPrecedes_facetLift_iff C
        (rationalExtend F (inertiaFixedField F) G)
        e a hequiv hapt hfacet hD hcommon Fc Fd).symm)
  map_rel_iff' := by
    intro Fd Fe
    exact B.facetPrecedes_facetLift_iff C
      (rationalExtend F (inertiaFixedField F) G)
      e a hequiv hapt hfacet hD hcommon Fd.val Fe.val

@[simp] theorem incidentFixedFacetOrderIso_val
    (Fc : BuildingFacet B) (Fd : IncidentFacets B Fc) :
    (incidentFixedFacetOrderIso A B e hfixed hsurj a hequiv hapt hfacet
      hD hcommon Fc Fd).val.val = B.facetLift C e Fd.val := rfl

end Langlands.Geometry.Building.MaximalUnramified.SemilinearApartmentData
