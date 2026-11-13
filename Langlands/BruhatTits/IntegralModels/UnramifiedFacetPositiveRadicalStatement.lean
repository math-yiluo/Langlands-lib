import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Monotonicity of the positive radical subgroups of descended facet models (KP 8.4.12, 9.5) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetPositiveRadicalAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Positive radical subgroups grow along incidence**
(Kaletha–Prasad Axiom 4.1.22(7) for the descended building, inclusion part: Corollary 8.4.12
and §9.5).

Let `G`, `P`, `R`, `T`, `C`, `A`, `e`, `a` and `E` be as in
`UnramifiedFacetParabolicImageStatement`, and write `B = P.toValuationBuildingData`. Let
`F ≺ F'` be facets of `B`, and `D`, `D'` relative-component model pairs over `𝒪[F]` with
smooth neutral models whose base changes to the integers of `K = inertiaFixedField F` have
the integral points `G(K)^0 ∩ G(K)_{e(F)}` and `G(K)^0 ∩ G(K)_{e(F')}`. For maximal
reductive quotients `Q`, `Q'` of the special fibres of their neutral models, the points of
`G(F)` given by integral sections of `D.neutral` reducing into the unipotent radical of `Q`
(the group `G(F)^{0+}_F`) lie in the corresponding group for `D'` and `Q'`. -/
def UnramifiedFacetPositiveRadicalStatement : Prop :=
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
      ∀ (Q : SpecialFibreQuotientData D) (Q' : SpecialFibreQuotientData D'),
        Q.IsReductiveQuotient → Q'.IsReductiveQuotient →
          Q.positivePoints ≤ Q'.positivePoints

end Langlands.BruhatTits.IntegralModels
