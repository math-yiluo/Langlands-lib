import Langlands.BruhatTits.IntegralModels.GeneralMorphismAxiomsUnramified
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof

/-! # KP Axiom 4.1.22 for a model family described over the maximal unramified integers

This module assembles the complete KP Axiom 4.1.22 (`SatisfiesMorphismAxioms`) for a
building model family over `𝒪[F]` whose neutral models have prescribed integral points
after base change to the integers of the maximal unramified extension. The inputs are the
statement of KP Proposition 8.4.15 over the maximal unramified integers
(`UnramifiedModelKernelStatement`) and the five facet-clause statements
`UnramifiedFacet*Statement`. Everything else is proved here or in the Library.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance morphismAxiomsUnramifiedAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance morphismAxiomsUnramifiedScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

variable (P : ParahoricBuildingData G) (R : P.toValuationBuildingData.PolysimplicialRealization)
  (T : P.toValuationBuildingData.ApartmentSplitting)
  (h1 : P.SatisfiesBuildingAxiom R) (h2 : P.HasBoundedOpenStabilizers)
  (h3 : P.SatisfiesAffineApartmentAxiom T) (h4 : P.HasRootReflections)
  (h5 : P.SatisfiesApartmentAxioms) (h6 : P.HasCompatibleApartmentFacets)
  (h7 : P.HasTitsSystem)

set_option maxHeartbeats 4000000 in
include h1 h2 h3 h4 h5 h6 h7 in
/-- **KP Axiom 4.1.22 from the unramified statements.** Let `P`, `R`, `T` satisfy the
seven predicates of the target statement, and let `C`, `A`, `e`, `a` satisfy the eight
conclusions of the apartment-compatible unramified descent. Let `M` be a building model
family over `𝒪[F]` such that, for one zero datum `E` and every index `Ω`, the base change of
the neutral model of `M.model Ω` to the maximal unramified integers has integral points
`E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`, and every integral torus of `M` satisfies the
torus clause of Axiom 4.1.20(3). Given `UnramifiedModelKernelStatement` and the five
facet-clause statements, there are special-fibre quotients `Q` of the facet models and
relative root reflection data `ρ` with `Q.SatisfiesMorphismAxioms ρ`. -/
theorem BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified
    (hker : UnramifiedModelKernelStatement.{u})
    (hS1 : UnramifiedFacetParabolicImageStatement.{u})
    (hS2 : UnramifiedFacetParabolicOrderStatement.{u})
    (hS3 : UnramifiedFacetCommonTorusStatement.{u})
    (hS4 : UnramifiedFacetRootDatumStatement.{u})
    (hS5 : UnramifiedFacetPositiveRadicalStatement.{u})
    (M : BuildingModelFamily P.toValuationBuildingData ↥𝒪[F])
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (A : MaximalUnramified.SemilinearApartmentData C)
    (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
    (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment)
    (he_inj : Function.Injective e)
    (he_smul : ∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (he_apt : ∀ w : P.toValuationBuildingData.Apartment,
      e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w))
    (hA_fix : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
        (z : P.toValuationBuildingData.ReducedBuilding),
      A.action σ (e z) = e z)
    (hA_surj : ∀ y : C.ReducedBuilding,
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y) →
        ∃ z : P.toValuationBuildingData.ReducedBuilding, e z = y)
    (hspecial : ∀ z : P.toValuationBuildingData.ReducedBuilding,
      C.IsSpecialPoint (e z) → P.toValuationBuildingData.IsSpecialPoint z)
    (hfacet : ∀ w : P.toValuationBuildingData.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
        AffineRootSystem.facet P.toValuationBuildingData.affineRoots w)
    (hkernel : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) P.S.toGrp),
      ∀ w : P.toValuationBuildingData.Apartment,
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i) s •
          e (P.toValuationBuildingData.apartmentMap w) =
            e (P.toValuationBuildingData.apartmentMap w))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (hpoints : ∀ Ω : BuildingModelIndex P.toValuationBuildingData,
      (M.model Ω).neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω.val))
    (htorus : ∀ (Ω : BuildingModelIndex P.toValuationBuildingData) (g : rationalPoints G)
      (Ωa : Set P.toValuationBuildingData.Apartment)
      (h : Ω.val = P.toValuationBuildingData.translatedApartmentMap g '' Ωa),
      (M.torus Ω g Ωa h).SatisfiesTorusClause) :
    ∃ (Q : BuildingModelQuotientFamily P.toValuationBuildingData M)
      (ρ : RelativeRootReflectionData P.toValuationBuildingData.i),
      Q.SatisfiesMorphismAxioms ρ := by
  choose Qd hQd using fun Fa : BuildingFacet P.toValuationBuildingData ↦
    SpecialFibreQuotientData.exists_isReductiveQuotient (M.facetModels.model Fa)
  obtain ⟨QF, hQF⟩ : ∃ QF : BuildingModelQuotientFamily P.toValuationBuildingData M,
      ∀ Fa, (QF.quotient Fa).IsReductiveQuotient := ⟨⟨Qd⟩, hQd⟩
  obtain ⟨ρ, -⟩ := relativeRootReflectionExistence F G
    P.toValuationBuildingData.isConnectedReductive P.toValuationBuildingData.S
    P.toValuationBuildingData.i P.toValuationBuildingData.isMaximalSplitTorus
  have hO : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  refine ⟨QF, ρ, satisfiesGeneralMorphismAxioms_of_unramified_of_axioms P R T
    h1 h2 h3 h4 h5 h6 h7 hker M C E e a he_smul he_apt hpoints, ?_⟩
  have hS1' := hS1 F G P R T h1 h2 h3 h4 h5 h6 h7 C A e a he_inj he_smul he_apt hA_fix
    hA_surj hspecial hfacet hkernel E
  have hS3' := hS3 F G P R T h1 h2 h3 h4 h5 h6 h7 C A e a he_inj he_smul he_apt hA_fix
    hA_surj hspecial hfacet hkernel E
  have hS4' := hS4 F G P R T h1 h2 h3 h4 h5 h6 h7 C A e a he_inj he_smul he_apt hA_fix
    hA_surj hspecial hfacet hkernel E
  have hS5' := hS5 F G P R T h1 h2 h3 h4 h5 h6 h7 C A e a he_inj he_smul he_apt hA_fix
    hA_surj hspecial hfacet hkernel E
  have hsm : ∀ Fc : BuildingFacet P.toValuationBuildingData,
      (M.facetModels.model Fc).neutral.IsSmooth := fun Fc =>
    (M.facetModels.model Fc).neutral_smooth
  have hpt : ∀ Fc : BuildingFacet P.toValuationBuildingData,
      (M.facetModels.model Fc).neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) := fun Fc =>
    hpoints (BuildingModelIndex.ofFacet Fc)
  refine
    { reductive_quotients := hQF
      parabolic_images := fun Fc Fc' h =>
        (hS1' Fc Fc' h _ _ (hsm Fc) (hsm Fc') (hpt Fc) (hpt Fc')
          (M.facetModels.morphism Fc Fc' h)).1
      common_tori := fun Fc Fc' h g Fa Fa' hface hF hF' => ?_
      lie_weight_signs := fun Fc Fc' h g Fa Fa' hface hF hF' hT =>
        ((hS3' Fc Fc' g Fa Fa' hface hF hF' _ _ (hsm Fc) (hsm Fc') (hpt Fc) (hpt Fc')
          (M.facetModels.morphism Fc Fc' h) (QF.quotient Fc)
          (M.torus (BuildingModelIndex.ofFacet Fc') g Fa' hF') (hQF Fc)
          (htorus _ g Fa' hF')).2.2 hT)
      reduction_preimages := fun Fc Fc' h =>
        (hS1' Fc Fc' h _ _ (hsm Fc) (hsm Fc') (hpt Fc) (hpt Fc')
          (M.facetModels.morphism Fc Fc' h)).2
      parabolic_order := fun Fc =>
        hS2 F G P R T h1 h2 h3 h4 h5 h6 h7 C A e a he_inj he_smul he_apt hA_fix
          hA_surj hspecial hfacet hkernel E M.facetModels (fun Fc => ⟨hsm Fc, hpt Fc⟩)
          Fc (QF.quotient Fc) (hQF Fc)
      derivative_root_data := fun Fc g Fa hFa hF hT =>
        hS4' Fc g Fa hFa hF _ (hsm Fc) (hpt Fc) (QF.quotient Fc)
          (M.torus (BuildingModelIndex.ofFacet Fc) g Fa hF) ρ (hQF Fc)
          (htorus _ g Fa hF) hT
      positive_radicals := fun Fc Fc' h =>
        ⟨IntegralModel.reduction_surjective _ (hsm Fc),
          IntegralModel.reduction_surjective _ (hsm Fc'),
          hS5' Fc Fc' h _ _ (hsm Fc) (hsm Fc') (hpt Fc) (hpt Fc')
            (QF.quotient Fc) (QF.quotient Fc') (hQF Fc) (hQF Fc')⟩ }
  have hT := htorus (BuildingModelIndex.ofFacet Fc') g Fa' hF'
  have key := hS3' Fc Fc' g Fa Fa' hface hF hF' _ _ (hsm Fc) (hsm Fc') (hpt Fc) (hpt Fc')
    (M.facetModels.morphism Fc Fc' h) (QF.quotient Fc)
    (M.torus (BuildingModelIndex.ofFacet Fc') g Fa' hF') (hQF Fc) hT
  exact ⟨hT.1, hT.2, key.1, key.2.1⟩

end Langlands.BruhatTits.IntegralModels
