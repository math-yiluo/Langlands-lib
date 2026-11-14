import Langlands.Geometry.Building.BuildingFacetRestrictionEmbedding
import Langlands.Geometry.Building.UnramifiedBuildingFacetRecovery
import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery

/-! # Recovering descended full facets from unramified zero fixers and model images -/

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
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

include hD hcommon hequiv hap hfac

/-- Equality of the actual unramified zero fixers of the images of two full
downstairs facets recovers those downstairs facets. -/
theorem descendedFacet_eq_of_zeroFixer_eq
    {Fc Fd : BuildingFacet B}
    (heq : E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val)) :
    Fc = Fd := by
  apply (B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac).injective
  exact E.buildingFacet_eq_of_zeroFixer_eq C
    (Fc.property.nonempty.image e)
    (B.image_subset_facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fc)
    (Fd.property.nonempty.image e)
    (B.image_subset_facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fd) heq

/-- Faithfully encode every downstairs full facet by the actual zero fixer of
its image in the supplied maximal-unramified building. -/
def descendedFacetZeroFixerEmbedding :
    BuildingFacet B ↪ Subgroup (rationalPoints H) where
  toFun Fc := E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)
  inj' := fun _ _ heq =>
    E.descendedFacet_eq_of_zeroFixer_eq B C ρ e a hD hcommon hequiv hap hfac heq

@[simp] theorem descendedFacetZeroFixerEmbedding_apply (Fc : BuildingFacet B) :
    E.descendedFacetZeroFixerEmbedding B C ρ e a hD hcommon hequiv hap hfac Fc =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) :=
  rfl

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
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
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

/-- Equality on all test schemes of the actual neutral special-fibre images
recovers downstairs facets, when the neutral integral-point characterizations
and both target congruence containments hold. -/
theorem descendedFacet_eq_of_unramifiedSpecialFibreImage_eq
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints)
    (heq : SubgroupFunctor.range φ.specialFibreImageInclusion =
      SubgroupFunctor.range ψ.specialFibreImageInclusion) :
    Fc = Fd := by
  apply E.descendedFacet_eq_of_zeroFixer_eq B C ρ e a hD hcommon hequiv hap hfac
  rw [← hsource₁, ← hsource₂]
  exact (φ.specialFibreImage_eq_iff_integralPoints_eq ψ hker₁ hker₂).mp heq

end Langlands.BruhatTits.IntegralModels
