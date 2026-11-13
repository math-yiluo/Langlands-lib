import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Parabolic order bijection for descended facet models (KP 9.3.2, Proposition 2.4.5, 8.4.19(4)) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetParabolicOrderAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Incident facets and parabolic subgroups of the maximal reductive quotient**
(Kaletha–Prasad §9.3.2 with Proposition 2.4.5, the descended form of Theorem 8.4.19(4)).

Let `G`, `P`, `R`, `T`, `C`, `A`, `e`, `a` and `E` be as in
`UnramifiedFacetParabolicImageStatement`, and write `B = P.toValuationBuildingData`. Let `Mf`
be facet model data over `𝒪[F]` for all facets of `B`, whose neutral models are smooth and
whose base changes to the integers of `K = inertiaFixedField F` have the integral points
`G(K)^0 ∩ G(K)_{e(F)}`. Then for every facet `F` and every maximal reductive quotient `Q` of
the special fibre of the neutral model for `F`, the map sending an incident facet `F ≺ F'` to
the image of `Mf.morphism F F'` in `Q` is a bijection onto all parabolic subgroups of `Q` over
the residue field of `𝒪[F]`, and incidence reverses inclusion. -/
def UnramifiedFacetParabolicOrderStatement : Prop :=
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
      (Mf : FacetModelData P.toValuationBuildingData ↥𝒪[F]),
      (∀ Fc : BuildingFacet P.toValuationBuildingData,
        (Mf.model Fc).neutral.IsSmooth ∧
          (Mf.model Fc).neutral.baseChangeUnramified.integralPoints =
            E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)) →
      ∀ (Fc : BuildingFacet P.toValuationBuildingData)
        (Q : SpecialFibreQuotientData (Mf.model Fc)),
        Q.IsReductiveQuotient →
          Mf.HasFacetParabolicOrderBijection Fc Q

end Langlands.BruhatTits.IntegralModels
