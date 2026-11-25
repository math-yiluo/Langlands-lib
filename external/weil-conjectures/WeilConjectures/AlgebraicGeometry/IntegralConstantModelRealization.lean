/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
public import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
public import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity
public import WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
public import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations
public import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
public import WeilConjectures.CategoryTheory.AbutmentImageFiltration
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
public import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.CategoryTheory.FinitePageGradedQuotient
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.CategoryTheory.HalfPlaneConvergence
public import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
public import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
public import WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
public import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
public import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
public import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
public import WeilConjectures.CategoryTheory.TowerSplitEnvelope
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
public import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.TruncationTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
public import WeilConjectures.RingTheory.FactorsThroughLocalization
public import WeilConjectures.RingTheory.FilteredColimitOfFactorization
public import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
public import WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower
public import WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions

/-! # Canonical integral constant-model realization

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), and the
projection-normalized integral coefficient comparison.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.IntegralConstantModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The spectral and absolute-value coefficient presentations have the same ring object.
Source: the projection-normalized integral coefficient comparison
(auxiliary; not a blueprint node). -/
theorem pointEquality :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E :=
  integralPointMon_eq l E

/-- The identity comparison of the two equal point coefficient presentations.
Source: the spectral-norm integral coefficient comparison
(auxiliary; not a blueprint node). -/
def pointComparison : Mon.mk (DerivedNakayama.integerRing l E) ≅ sfbCondensedIntegers l E :=
  eqToIso (pointEquality l E)

/-- The actual section-and-coefficient functor; its action changes only scalar actions.
Source: the normalized coefficient projections of the integral criterion
(auxiliary; not a blueprint node). -/
def modulesFunctor (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (sfbCondensedIntegers l E).X X) ⥤
      Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) :=
  Mod.comap (coefficientMap (pointComparison l E).hom.hom X) ⋙
    integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom ⋙
    Scheme.pbcRestrict (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom

/-- Each coefficient map used by the functor is an isomorphism.
Source: the finite-projection integral coefficient comparisons
(auxiliary; not a blueprint node). -/
instance modulesFunctor_isEquivalence (X : Scheme.{u}) :
    (modulesFunctor l E X).IsEquivalence := by
  have : (Mod.comap (coefficientMap (pointComparison l E).hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (coefficientMap (pointComparison l E).hom.hom X)).isEquivalence_functor
  have : (Scheme.pbcRestrict
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom).IsEquivalence :=
    restriction_isEquivalence ((Scheme.adicLisseForget X).mapIso
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)))
  have : (integralSectionFunctor l E X).IsEquivalence :=
    (integralSectionFunctor_properties l E X).2
  have : (SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).IsEquivalence :=
    restriction_isEquivalence (Scheme.integralDetailedCoefficientComparison X l E)
  unfold modulesFunctor
  exact Functor.isEquivalence_trans _ _

/-- The ordinary realization preserves addition, since all its factors preserve products.
Source: Stacks Tag 00YV
(auxiliary; not a blueprint node). -/
instance modulesFunctor_additive (X : Scheme.{u}) : (modulesFunctor l E X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Termwise localization of the canonical ordinary realization.
Source: Stacks Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
def derived (X : Scheme.{u}) := (modulesFunctor l E X).mapDerivedCategory.asEquivalence

end AlgebraicGeometry.ProEtale.IntegralConstantModel
