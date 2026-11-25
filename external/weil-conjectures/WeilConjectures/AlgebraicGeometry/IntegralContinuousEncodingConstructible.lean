/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicLisseModule
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletion
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport
import WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
import WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity
import WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import WeilConjectures.AlgebraicGeometry.StrictTowerOperations
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import WeilConjectures.CategoryTheory.AbutmentImageFiltration
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
import WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.SectionActionInternal
import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
import WeilConjectures.CategoryTheory.TowerSplitEnvelope
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower
import WeilConjectures.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing

set_option linter.privateModule false

/-! # Constructibility under continuous integral section encoding

Source: Bhatt--Scholze, Definition 6.8.10; Stacks Project, Tag 00YV.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  Scheme.integralDetailedCoefficientComparison

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

private noncomputable def pointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }

attribute [local irreducible] pointIntegerIso

private theorem integral_internal_constant_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [EssentiallySmall.{u + 1} X.ProEt] [IsNoetherian X]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstructibleModuleObject (AdicCompletion.ring l E X) M) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  let e := pointIntegerIso l E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have h := integralLfpConstantModelComparison l E X ((Mod.comap ψ).obj M)
  exact (constantModel_comap_iff φ X M).mp
    (h.mp (_root_.constructible_comap ψ hM))

end AlgebraicGeometry.ProEtale
