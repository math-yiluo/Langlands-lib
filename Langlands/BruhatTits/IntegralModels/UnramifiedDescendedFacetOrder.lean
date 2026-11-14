import Langlands.Geometry.Building.ValuationBuildingFacetIncidenceEmbedding
import Langlands.Geometry.Building.UnramifiedBuildingFacetRecovery
import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery

/-! # Reverse incidence from descended zero fixers and actual model images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  (ρ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : B.HasCommonApartments)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

include hD hcommon hequiv hap hfac

/-- Containment of the actual unramified zero fixers of full downstairs
facet images forces reverse incidence of those downstairs facets. -/
theorem facetPrecedes_of_descendedZeroFixer_le
    {Fc Fd : BuildingFacet B}
    (hle : E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) ≤
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val)) :
    FacetPrecedes B Fd Fc := by
  apply (B.facetPrecedes_facetLift_iff C ρ e a hequiv hap hfac hD hcommon Fd Fc).mp
  have hsub (Fe : BuildingFacet B) :
      e '' Fe.val ⊆ (B.facetLift C e Fe).val := by
    rw [B.image_facetLift C ρ e a hequiv hap hfac hD hcommon Fe]
    exact Set.inter_subset_left
  exact E.facetPrecedes_of_buildingZeroFixer_le C
    (Fc.property.nonempty.image e) (hsub Fc)
    (Fd.property.nonempty.image e) (hsub Fd) hle

/-- The actual zero-fixer assignment on images of downstairs full facets
reflects reverse incidence. -/
def HasDescendedFacetZeroFixerOrderReflection : Prop :=
  ∀ Fc Fd : BuildingFacet B,
    E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) ≤
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val) →
        FacetPrecedes B Fd Fc

theorem hasDescendedFacetZeroFixerOrderReflection :
    E.HasDescendedFacetZeroFixerOrderReflection B C e := by
  intro Fc Fd hle
  exact E.facetPrecedes_of_descendedZeroFixer_le B C ρ e a
    hD hcommon hequiv hap hfac hle

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels

open Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  (ρ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : B.HasCommonApartments)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  {R : Type u} [CommRing R] [IsDomain R]
  [Algebra R (UnramifiedClosure F)] [IsFractionRing R (UnramifiedClosure F)]
  [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {source₁ source₂ target : RelativeComponentModelData R (UnramifiedClosure F) H}
  (φ : RelativeComponentModelHom source₁ target)
  (ψ : RelativeComponentModelHom source₂ target)

include hD hcommon hequiv hap hfac

/-- Containment on every test scheme of actual special-fibre images gives
reverse downstairs facet incidence under the displayed characterizations and
both target congruence containments. -/
theorem facetPrecedes_of_unramifiedSpecialFibreImage_le
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints)
    (hle : SubgroupFunctor.range φ.specialFibreImageInclusion ≤
      SubgroupFunctor.range ψ.specialFibreImageInclusion) :
    FacetPrecedes B Fd Fc := by
  apply E.facetPrecedes_of_descendedZeroFixer_le B C ρ e a
    hD hcommon hequiv hap hfac (Fc := Fc) (Fd := Fd)
  rw [← hsource₁, ← hsource₂]
  exact (φ.specialFibreImage_le_iff_integralPoints_le ψ hker₁ hker₂).mp hle

end Langlands.BruhatTits.IntegralModels
