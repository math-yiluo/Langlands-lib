/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedTensor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.AmpleFiniteAffineCover
import WeilConjectures.AlgebraicGeometry.AmpleIdealSection
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.BoundaryCechInjectiveMiddle
import WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit
import WeilConjectures.AlgebraicGeometry.BoundaryCoefficientTensorProduct
import WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorUnit
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.AlgebraicGeometry.CechH1Injective
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsEpi
import WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ComponentIntersectionsFinite
import WeilConjectures.AlgebraicGeometry.ComponentSupportedAffineSection
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
import WeilConjectures.AlgebraicGeometry.ConstructibleColimitFactorization
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations
import WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import WeilConjectures.AlgebraicGeometry.DerivedGlobalGermExchange
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import WeilConjectures.AlgebraicGeometry.EtaleSectionGermIso
import WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleSplitResiduePoints
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.FiniteClosedImmersionNearFibre
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import WeilConjectures.AlgebraicGeometry.FractionZeroTensorPower
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlueComponentLineBundles
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.IntegralDimOneAmple
import WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.ObjectSectionsNaturality
import WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import all WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractions
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition
import WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.AlgebraicGeometry.SquareZeroQuotientLocalAction
import WeilConjectures.AlgebraicGeometry.SquareZeroTensorSectionProductComparison
import WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictLocalDerivedGlobalExchange
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.TensorPullbackPowerAppend
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.AlgebraicGeometry.ZeroDimNoetherianAffine
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.ResolvedBoundaryNaturality
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.ConstructibleSheaf.AffineStratification
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective
import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import WeilConjectures.FieldTheory.SeparableSmoothColimit
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import WeilConjectures.Mathlib.CategoryTheory.Extensive
import WeilConjectures.RepresentationTheory.PrimaryPGroupFiltration
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import WeilConjectures.RingTheory.GradedPrimeAvoidance
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import WeilConjectures.RingTheory.RegularLocalOfFormallySmoothAdic
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.Topology.InverseImageOperationExt
import WeilConjectures.Topology.InverseImageRegularExtension
import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing

set_option linter.privateModule false

/-!
# Constructibility of proper ell-adic direct-image cohomology

This is the constructibility assertion of proper finiteness, separated from the
uniform cohomological-dimension estimate.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj
  Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open _root_.DerivedCategory CategoryTheory.Pretriangulated in
private lemma proper_bounded_induction (P : ObjectProperty (_root_.DerivedCategory C))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (h : ∀ G : C, P ((singleFunctor C 0).obj G)) (K : _root_.DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] : P K := by
  exact prop_of_bounded P ⊤ (fun G _ ↦ h G) K
    ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩ (fun _ ↦ trivial)

private theorem proper_finite_field_tor
    (F : Type (u + 1)) [Field F] (X : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, -⟩ := hK
  refine proper_bounded_induction _ (fun G ↦ ?_) K a b
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance

/-- The prime `l` vanishes in the residue field of the integers of a finite extension
of `ℚ_l`: its absolute value `1 / l` is below one, so it lies in the maximal ideal. -/
private noncomputable def continuousRingIso
    {A B : Type u} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

private noncomputable def continuousSmallRingIso
    {A : Type u} {B : Type} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

@[irreducible] private noncomputable def integerLatticeIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (ProEtale.integralCondensedRing l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := ProEtale.latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let e : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.val.ofAbs, x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ x.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact continuousRingIso e he.continuous he'.continuous

private theorem integerModel_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X)) :
    IsConstructibleModuleObject (condensedRingObj
      (ProEtale.DerivedNakayama.integerRing l E) X) M ↔
      ProEtale.IsConstantModelConstructible (ProEtale.DerivedNakayama.integerRing l E) X M :=
  ProEtale.comparison_transport (integerLatticeIso l E) X
    (ProEtale.integralLfpConstantModelComparison l E X) M

@[irreducible] private noncomputable def integerNormedIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCoeff.{u} l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l (ULift.{u} E)) := by
  let F := ULift.{u} E
  let : FiniteDimensional ℚ_[l] F :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  letI : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  letI : NormedAlgebra ℚ_[l] F := ⟨fun a x ↦ norm_smul_le a x.down⟩
  have hn (x : F) : spectralNorm ℚ_[l] F x = ‖x.down‖ :=
    (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (L := F) x).symm
  have hm (x : F) : x ∈ Padic.coefficientExtensionIntegers l F ↔
      x.down ∈ continuousIntegers l E := by
    have h := Padic.mem_coefficientExtensionIntegers l F x
    change _ ↔ ‖x.down‖₊ ≤ 1
    rw [h]
    change spectralNorm ℚ_[l] F x ≤ 1 ↔ _
    rw [hn]
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x.down‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x.down‖₊ ≤ 1)
  let A := ProEtale.latticeCoefficientIntegers l F
  let e : A ≃+* continuousIntegers l E :=
    { toFun := fun x ↦ ⟨x.val.ofAbs.down, (hm x.val.ofAbs).mp x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ (ULift.up x.val), (hm _).mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    change ‖x.val.ofAbs.down‖ = spectralNorm ℚ_[l] F x.val.ofAbs
    exact (hn x.val.ofAbs).symm
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact (continuousSmallRingIso e he.continuous he'.continuous).symm ≪≫
    integerLatticeIso l F

/-- A prime different from the characteristic of `k` is a unit in every stalk of a
scheme over `k`. -/
private theorem constructible_derived_extend
    (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S))
    (e : (Mod.extendScalars φ).leftDerivedFunctor.obj K ≅ L)
    (q : ℤ) (h : IsConstructibleModuleObject R
      ((DerivedCategory.homologyFunctor _ q).obj K)) :
    IsConstructibleModuleObject S ((DerivedCategory.homologyFunctor _ q).obj L) := by
  have h' := ProEtale.constructible_extend R S φ h
  have h'' := _root_.constructible_of_iso
    (((Mod.extendScalars φ).leftDerivedFunctorHomologyFunctorIso q).app K) h'
  exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e) h''

end AlgebraicGeometry.ProEtale.CondensedRing
