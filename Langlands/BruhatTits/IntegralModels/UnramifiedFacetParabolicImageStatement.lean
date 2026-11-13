import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Parabolic special-fibre images of descended facet models (KP 8.4.19(2),(3), 9.3.2–9.3.3) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetParabolicImageAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Parabolic special-fibre images and reduction preimages for incident facets**
(Kaletha–Prasad Theorem 8.4.19(2),(3), descended to `𝒪[F]` by §9.3.2 and Proposition 9.3.3).

Let `G` be an affine group over a nonarchimedean local field `F`, with building data `P`
satisfying the seven Library predicates of the target `IntegralModelAxiomsStatement`; write
`B = P.toValuationBuildingData`. Let `K = inertiaFixedField F` and let `C`, `A`, `e`, `a` be
building data of `G_K`, a semilinear Galois action on it, an embedding of reduced buildings
and an affine map of apartments with the eight conclusions of
`Langlands.Geometry.Building.UnramifiedApartmentDescentStatement`, and let `E` compute
`G(K)^0`. Let `F ≺ F'` be facets of `B`. Let `D` and `D'` be relative-component model pairs
over `𝒪[F]` with smooth neutral models whose base changes to the integers of `K` have the
integral points `G(K)^0 ∩ G(K)_{e(F)}` and `G(K)^0 ∩ G(K)_{e(F')}`. Then for every model
morphism `φ : D' → D` (identity on generic fibres), the schematic image of the special-fibre
map of the neutral models is a parabolic subgroup of the special fibre of `D.neutral`, and
the integral sections of `D.neutral` reducing into the residue-field points of that image are
exactly the image of the integral sections of `D'.neutral`. -/
def UnramifiedFacetParabolicImageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting),
    P.SatisfiesBuildingAxiom R →
    P.HasBoundedOpenStabilizers →
    P.SatisfiesAffineApartmentAxiom T →
    P.HasRootReflections →
    P.SatisfiesApartmentAxioms →
    P.HasCompatibleApartmentFacets →
    P.HasTitsSystem →
    ∀ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (A : MaximalUnramified.SemilinearApartmentData C)
      (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
      (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment),
      Function.Injective e →
      (∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
        e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) →
      (∀ w : P.toValuationBuildingData.Apartment,
        e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w)) →
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
          (z : P.toValuationBuildingData.ReducedBuilding),
        A.action σ (e z) = e z) →
      (∀ y : C.ReducedBuilding,
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y) →
          ∃ z : P.toValuationBuildingData.ReducedBuilding, e z = y) →
      (∀ z : P.toValuationBuildingData.ReducedBuilding,
        C.IsSpecialPoint (e z) → P.toValuationBuildingData.IsSpecialPoint z) →
      (∀ w : P.toValuationBuildingData.Apartment,
        a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
          AffineRootSystem.facet P.toValuationBuildingData.affineRoots w) →
      (∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) P.S.toGrp),
        ∀ w : P.toValuationBuildingData.Apartment,
          rationalPoints.map
              ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i) s •
            e (P.toValuationBuildingData.apartmentMap w) =
              e (P.toValuationBuildingData.apartmentMap w)) →
    ∀ (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
      (Fc Fc' : BuildingFacet P.toValuationBuildingData),
      FacetPrecedes P.toValuationBuildingData Fc Fc' →
    ∀ (D D' : RelativeComponentModelData ↥𝒪[F] F G),
      D.neutral.IsSmooth → D'.neutral.IsSmooth →
      D.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
      D'.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val) →
      ∀ φ : RelativeComponentModelHom D' D,
        φ.HasParabolicSpecialFibreImage ∧ φ.HasParabolicReductionPreimage

end Langlands.BruhatTits.IntegralModels
