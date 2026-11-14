import Langlands.Geometry.Building.UnramifiedDescentAffineApartment
import Langlands.Geometry.Building.UnramifiedDescentFixedImage
import Langlands.Geometry.Building.UnramifiedApartmentDescentStatement
import Langlands.Geometry.Building.AffineRootRestriction
import Langlands.Geometry.Building.BuildingSpecialPointComparison
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint

/-! # Apartment-compatible descent from fixed restriction data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance assemblyExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- A witness carrying all eight conclusions of apartment-compatible descent. -/
structure ApartmentDescentData (B : ValuationBuildingData G) where
  building : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)
  semilinear : MaximalUnramified.SemilinearApartmentData building
  embedding : B.ReducedBuilding → building.ReducedBuilding
  apartment : B.Apartment →ᵃ[ℝ] building.Apartment
  injective : Function.Injective embedding
  equivariant : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    embedding (g • z) = rationalExtend F (inertiaFixedField F) G g • embedding z
  apartment_compatible : ∀ w : B.Apartment,
    embedding (B.apartmentMap w) = building.apartmentMap (apartment w)
  fixed : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (z : B.ReducedBuilding),
    semilinear.action σ (embedding z) = embedding z
  surjective_fixed : ∀ y : building.ReducedBuilding,
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, semilinear.action σ y = y) →
      ∃ z : B.ReducedBuilding, embedding z = y
  special : ∀ z : B.ReducedBuilding,
    building.IsSpecialPoint (embedding z) → B.IsSpecialPoint z
  facets : ∀ w : B.Apartment,
    apartment ⁻¹' AffineRootSystem.facet building.affineRoots (apartment w) =
      AffineRootSystem.facet B.affineRoots w
  torus_units : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) B.S.toGrp), ∀ w : B.Apartment,
    rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
      embedding (B.apartmentMap w) = embedding (B.apartmentMap w)

variable [Smooth G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (hE : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (B : ValuationBuildingData G) (f : B.S ⟶ T)
  (hcar : ∀ ψ : RootFunctionFamily B.S G, ψ ∈ B.apartment.carrier ↔
    ∃ x : D.Apartment, apartmentGaloisFixed D x ∧ ψ = apartmentRestriction hiT hE D B f x)
  (hinj : ∀ x y : D.Apartment, apartmentGaloisFixed D x → apartmentGaloisFixed D y →
    apartmentRestriction hiT hE D B f x = apartmentRestriction hiT hE D B f y → x = y)
  (hroots : AffineRootSystem.restrictedRoots (descentAffineMap hiT hE D B f hcar hinj)
    D.affineRoots = B.affineRoots)

include hroots in
/-- Actual affine-root restriction gives exactly the required facet preimages. -/
theorem descentAffineMap_facets (w : B.Apartment) :
    (descentAffineMap hiT hE D B f hcar hinj) ⁻¹'
        AffineRootSystem.facet D.affineRoots (descentAffineMap hiT hE D B f hcar hinj w) =
      AffineRootSystem.facet B.affineRoots w := by
  rw [← hroots]
  exact (AffineRootSystem.facet_restrictedRoots_eq_preimage _ _ w).symm

include hroots in
/-- Actual affine-root restriction also reflects specialness of an apartment image. -/
theorem descentAffineMap_isSpecialPoint (w : B.Apartment)
    (hw : D.IsSpecialBuildingPoint
      (D.apartmentMap (descentAffineMap hiT hE D B f hcar hinj w))) :
    AffineRootSystem.IsSpecialPoint B.affineRoots w := by
  exact AffineRootSystem.isSpecialPoint_of_restrictedRoots_eq
    (descentAffineMap hiT hE D B f hcar hinj) hroots
    (fun _ h => Langlands.BruhatTits.SpecialCompact.affineRoot_linear_ne_zero_of_split
      hiT.isSplitSubtorus.1 _ D h)
    ((D.isSpecialBuildingPoint_apartmentMap_iff _).mp hw)

variable
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
  (hf : CommGroupScheme.groupHom f ≫ iT = B.i)
  (hnorm : ∀ (n : normalizerPoints B.i) (x : D.Apartment), apartmentGaloisFixed D x →
    ∃ y : D.Apartment, apartmentGaloisFixed D y ∧
      D.apartmentMap y = rationalExtend F (inertiaFixedField F) G
        (n : rationalPoints G) • D.apartmentMap x ∧
      apartmentRestriction hiT hE D B f y = n • apartmentRestriction hiT hE D B f x)
  (hfilt : ∀ (x : D.Apartment) (w : B.Apartment),
    w.val = apartmentRestriction hiT hE D B f x → ∀ a : relativeRoots B.i,
      B.filtration w a 0 ≤ (D.sharpFixer {x}).comap
        (rationalExtend F (inertiaFixedField F) G))
  (hK : Function.Injective D.apartmentMap)
  (hB : ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R)
  (hfixpt : ∀ y : D.ReducedBuilding,
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
    ∃ (g : rationalPoints G) (x : D.Apartment), apartmentGaloisFixed D x ∧
      rationalExtend F (inertiaFixedField F) G g • D.apartmentMap x = y)

/-- Assemble all eight clauses from fixed restriction, the original quotient descent
premises and actual affine-root restriction. -/
def apartmentDescentData : ApartmentDescentData B where
  building := buildingData iT hGK hiT D C h6
  semilinear := semilinearData iT hGK hiT C h6 hD
  embedding := descentMap hGK hiT C h6 B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt
  apartment := descentAffineMap hiT hE D B f hcar hinj
  injective := descentMap_injective hGK hiT C h6 B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt hK hB
  equivariant := descentMap_smul hGK hiT C h6 B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt
  apartment_compatible := descentMap_apartment hGK hiT C h6 B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt
  fixed := descentMap_fixed hGK hiT C h6 hD B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt (fun _ hx => hx)
  surjective_fixed := descentMap_surjective_fixed hGK hiT C h6 hD B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt hfixpt
  special := descentMap_isSpecialPoint hGK hiT C h6 B (apartmentGaloisFixed D)
    (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt (by
      intro x w hx hw hs
      apply descentAffineMap_isSpecialPoint hiT hE D B f hcar hinj hroots w
      change D.IsSpecialBuildingPoint
        (D.apartmentMap (descentPoint B (apartmentGaloisFixed D)
          (apartmentRestriction hiT hE D B f) hcar w))
      rw [descentPoint_eq B (apartmentGaloisFixed D)
        (apartmentRestriction hiT hE D B f) hcar hinj hx w hw]
      exact hs)
  facets := descentAffineMap_facets hiT hE D B f hcar hinj hroots
  torus_units := by
    intro s hs w
    exact descentMap_torusUnits hGK hiT C h6 B (apartmentGaloisFixed D)
      (apartmentRestriction hiT hE D B f) hcar hinj hnorm hfilt f hf s hs w

end Langlands.Geometry.Building.UnramifiedBuildingDescent
