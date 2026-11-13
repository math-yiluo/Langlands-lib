import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Common maximal split tori and Lie-weight signs for descended facet models (KP 8.4.19, 9.4) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetCommonTorusAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Common maximal split tori and the Lie-weight sign formula for incident facets**
(Kaletha–Prasad Axiom 4.1.22(3) for the descended building: Theorem 8.4.10, Theorem 8.4.19
and the descent of §§9.2.5, 9.3.2 and 9.4).

Let `G`, `P`, `R`, `T`, `C`, `A`, `e`, `a` and `E` be as in
`UnramifiedFacetParabolicImageStatement`, and write `B = P.toValuationBuildingData`. Let
`F ≺ F'` be facets of `B` presented in the translated apartment `g • A(S)` by apartment
facets `Fa`, a face of `Fa'`. Let `D`, `D'` be relative-component model pairs over `𝒪[F]`
with smooth neutral models whose base changes to the integers of `K = inertiaFixedField F`
have the integral points `G(K)^0 ∩ G(K)_{e(F)}` and `G(K)^0 ∩ G(K)_{e(F')}`. Let
`φ : D' → D` be a model morphism, `Q` a maximal reductive quotient of the special fibre of
`D.neutral`, and `𝒯` an integral torus of `D'` with generic fibre `S` included by `Int(g) ∘ i`
satisfying the torus clause of Axiom 4.1.20(3). Then the special fibre of `𝒯` is a maximal
split torus of the special fibre of `D.neutral` and of `Q`, through `φ`, and the nonzero
weights of `S` on the Lie algebra of the image of `φ` in `Q` are the roots of `Q` that are
nonnegative on every vector carrying a point of `Fa` into `Fa'`. -/
def UnramifiedFacetCommonTorusStatement : Prop :=
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
      (Fc Fc' : BuildingFacet P.toValuationBuildingData)
      (g : rationalPoints G) (Fa Fa' : Set P.toValuationBuildingData.Apartment),
      AffineRootSystem.IsFaceOf P.toValuationBuildingData.affineRoots Fa Fa' →
      Fc.val = P.toValuationBuildingData.translatedApartmentMap g '' Fa →
      Fc'.val = P.toValuationBuildingData.translatedApartmentMap g '' Fa' →
    ∀ (D D' : RelativeComponentModelData ↥𝒪[F] F G),
      D.neutral.IsSmooth → D'.neutral.IsSmooth →
      D.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
      D'.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val) →
      ∀ (φ : RelativeComponentModelHom D' D) (Q : SpecialFibreQuotientData D)
        (𝒯 : IntegralTorusData D' P.toValuationBuildingData.S
          (P.toValuationBuildingData.i ≫ (G.innerIso g).hom)),
        Q.IsReductiveQuotient → 𝒯.SatisfiesTorusClause →
          IsMaximalSplitTorus (φ.targetTorusInclusion 𝒯) ∧
            IsMaximalSplitTorus (φ.quotientTorusInclusion Q 𝒯) ∧
            ∀ hT : IsSplitTorus 𝒯.torus.toGrp,
              φ.HasApartmentLieWeightSignFormula P.toValuationBuildingData Q 𝒯 hT Fa Fa'

end Langlands.BruhatTits.IntegralModels
