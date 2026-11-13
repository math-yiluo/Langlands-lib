import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The derivative root datum of a descended facet model (KP 8.4.10, Proposition 9.4.23) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetRootDatumAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The root datum of the maximal reductive quotient of a facet model**
(Kaletha–Prasad Axiom 4.1.22(6) for the descended building: Theorem 8.4.10 and
Proposition 9.4.23).

Let `G`, `P`, `R`, `T`, `C`, `A`, `e`, `a` and `E` be as in
`UnramifiedFacetParabolicImageStatement`, and write `B = P.toValuationBuildingData`. Let `F`
be a facet of `B` presented in the translated apartment `g • A(S)` by the apartment facet
`Fa`. Let `D` be a relative-component model pair over `𝒪[F]` with smooth neutral model whose
base change to the integers of `K = inertiaFixedField F` has the integral points
`G(K)^0 ∩ G(K)_{e(F)}`, `Q` a maximal reductive quotient of the special fibre of `D.neutral`,
`𝒯` an integral torus of `D` with generic fibre `S` included by `Int(g) ∘ i` satisfying the
torus clause of Axiom 4.1.20(3), and `Droot` any relative root reflection data of `i`. Then
the root datum of `Q` relative to the image of the special fibre of `𝒯` consists exactly of
the derivatives of the affine roots vanishing on `Fa` and their coroots in `Droot`, both
transported through `𝒯`. -/
def UnramifiedFacetRootDatumStatement : Prop :=
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
      (Fc : BuildingFacet P.toValuationBuildingData)
      (g : rationalPoints G) (Fa : Set P.toValuationBuildingData.Apartment),
      AffineRootSystem.IsFacet P.toValuationBuildingData.affineRoots Fa →
      Fc.val = P.toValuationBuildingData.translatedApartmentMap g '' Fa →
    ∀ D : RelativeComponentModelData ↥𝒪[F] F G,
      D.neutral.IsSmooth →
      D.neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
      ∀ (Q : SpecialFibreQuotientData D)
        (𝒯 : IntegralTorusData D P.toValuationBuildingData.S
          (P.toValuationBuildingData.i ≫ (G.innerIso g).hom))
        (Droot : RelativeRootReflectionData P.toValuationBuildingData.i),
        Q.IsReductiveQuotient → 𝒯.SatisfiesTorusClause →
        ∀ hT : IsSplitTorus 𝒯.torus.toGrp,
          HasApartmentDerivativeRootDatum P.toValuationBuildingData Q 𝒯 Droot hT Fa

end Langlands.BruhatTits.IntegralModels
