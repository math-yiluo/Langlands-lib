/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
public import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
public import WeilConjectures.AlgebraicGeometry.PrimitiveRootsCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import WeilConjectures.AlgebraicGeometry.PurTwistSheaves
public import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjection
public import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
public import WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
public import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
public import WeilConjectures.CategoryTheory.SectionwisePushout
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import WeilConjectures.CategoryTheory.StageSystem.Shift
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
public import WeilConjectures.Mathlib.LinearAlgebra.Lagrange
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import WeilConjectures.SecSmoothPurity.NormalizedScalarTensorTransitions
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity
import WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleRestrictedTensorFiniteLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import WeilConjectures.AlgebraicGeometry.StrictTowerOperations
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.AbutmentImageFiltration
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.ConstantLeftModuleTransport
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.IntegerShiftFromOne
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.CategoryTheory.Monoidal.UnitComparison
import WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import WeilConjectures.CategoryTheory.Sites.TorsionSheafConstantModule
import WeilConjectures.CategoryTheory.TowerSplitEnvelope
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.ConstructibleSheaf.LisseRankOne
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.NumberTheory.Padics.IntegersModPow
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.RingTheory.NilpotentTorsionDerivedLimitComplete
import WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Finite levels and integral and rational Tate twist objects

Source: blueprint `definition-tate-twists`. The index n denotes exponent n+1.
The integral levels use the finite quotient tensor with the roots, restricted
along O_X -> B_X. The integral object is their limit in O_X-modules, and the
rational object is its specified extension of scalars. These are the original
constructions re-exported by `ProEtaleTateTwists`, with unchanged data and names.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The standard size witness at the coefficient universe, used with explicit universes.
This merely exposes Mathlib's existing small-category witness to instance search;
it avoids selecting an unrelated instance with an unconstrained extra universe.
Source: prose-01-10 and the small pro-etale site
(blueprint: definition-tate-twists). -/
instance spProEtEssentiallySmall : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} X.ProEt

/-- The cofinal ell-power ideals in the ring of integers.
Source: blueprint integral-twist formula (blueprint: definition-tate-twists). -/
def spTateEllIdeal (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Ideal (PadicAlgCl.integers ℓ E.1) :=
  Ideal.span { (ℓ : PadicAlgCl.integers ℓ E.1) ^ (n + 1) }

/-- The finite coefficient B_E,n+1 = O_E / ell^(n+1).
Source: blueprint integral-twist formula (blueprint: definition-tate-twists). -/
abbrev spEllQuotient (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (PadicAlgCl.integers ℓ E.1) ⧸ spTateEllIdeal ℓ E n

/-- The integer-ring topology inherited from its specified embedding in Qbar.
Source: blueprint coefficient convention (blueprint: definition-tate-twists). -/
@[instance_reducible] def spIntegersTopology (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    TopologicalSpace (PadicAlgCl.integers ℓ E.1) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  inferInstance

/-- Positive ell-power quotients are finite and their quotient maps are continuous
for the discrete target topology.
Source: blueprint cofinal-ideal paragraph (blueprint: definition-tate-twists).
Proof: write ell = v*pi^e with v a unit and e positive, using the DVR of the
coefficient-extension node. Then (ell^(n+1)) = (pi^(e*(n+1))). Finiteness is the
finite-quotient theorem for that positive exponent. The ideal is open in the
valuation topology, so each quotient fibre is open. This is continuity into the
discrete quotient, for the same extending valuation. -/
theorem spEllQuotient_finite_continuous (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) :
    Finite (spEllQuotient ℓ E n) ∧
    @Continuous _ _ (spIntegersTopology ℓ E) ⊥
      (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  have hq : Continuous (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) :=
    PadicAlgCl.continuous_integersModPowMk ℓ E.1 (n + 1)
  refine ⟨?_, hq⟩
  have : CompactSpace (PadicAlgCl.integers ℓ E.1) :=
    PadicAlgCl.compactSpace_integers ℓ E.1
  have himage : IsCompact (Set.univ : Set (spEllQuotient ℓ E n)) := by
    rw [← Set.range_eq_univ.mpr (Ideal.Quotient.mk_surjective
      (I := spTateEllIdeal ℓ E n))]
    exact isCompact_range hq
  have : CompactSpace (spEllQuotient ℓ E n) := ⟨himage⟩
  exact finite_of_compact_of_discrete

/-- The discrete finite coefficient as a continuous-function condensed ring.
It is canonically the constant finite ring sheaf, since continuous maps to a
finite discrete set are locally constant.
Source: blueprint finite-coefficient convention (blueprint: definition-tate-twists). -/
def spEllPointRing (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  Profinite.continuousMapRingSheaf (spEllQuotient ℓ E n)

/-- The abelian ring object underlying the finite condensed coefficient.
Source: blueprint finite-coefficient convention (blueprint: definition-tate-twists). -/
abbrev spEllPointRingObj (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (spEllPointRing ℓ E n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual continuous quotient map on condensed coefficients.
Source: blueprint coordinatewise quotient action (blueprint: definition-tate-twists). -/
def spEllPointReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ spEllPointRingObj ℓ E n :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk (spTateEllIdeal ℓ E n))
        (spEllQuotient_finite_continuous ℓ E n).2)

attribute [local irreducible] spEllPointReduction

set_option backward.isDefEq.respectTransparency false in
/-- The condensed finite quotient map preserves the ring structure.
Source: blueprint quotient action (blueprint: definition-tate-twists).
Proof: its maps are postcomposition with a ring homomorphism, so preserve one
and multiplication sectionwise; forgetting to abelian sheaves retains these laws. -/
@[instance] theorem spEllPointReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointReduction.{u} ℓ E n) := by
  unfold spEllPointReduction
  infer_instance

/-- The pulled-back reduction O_E,X -> (B_E,n+1)_X.
Source: blueprint quotient action (blueprint: definition-tate-twists). -/
abbrev spEllReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  coefficientMap.{u} (spEllPointReduction.{u} ℓ E n) X

/-- Successive positive ell-power ideals are nested.
Source: blueprint quotient transitions (blueprint: definition-tate-twists).
Proof: ell^(n+2) = ell^(n+1)*ell lies in the ideal generated by ell^(n+1).
The span universal property gives the inclusion. -/
theorem spTateEllIdeal_succ_le (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spTateEllIdeal ℓ E (n + 1) ≤ spTateEllIdeal ℓ E n := by
  exact Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (ℓ : PadicAlgCl.integers ℓ E.1) (Nat.le_succ (n + 1)))

/-- The finite coefficient reduction at the point, induced by the identity on O_E.
Source: blueprint quotient transitions (blueprint: definition-tate-twists). -/
def spEllPointTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointRingObj.{u} ℓ E (n + 1) ⟶ spEllPointRingObj ℓ E n :=
  letI : TopologicalSpace (spEllQuotient ℓ E (n + 1)) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E (n + 1)) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E (n + 1)) := DiscreteTopology.topologicalRing
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Ideal.Quotient.factor (spTateEllIdeal_succ_le ℓ E n)) continuous_of_discreteTopology)

attribute [local irreducible] spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
/-- Finite reduction preserves one and multiplication.
Source: blueprint quotient transitions (blueprint: definition-tate-twists).
Proof: it is postcomposition with the quotient ring homomorphism; ring operations
on continuous functions are pointwise. -/
@[instance] theorem spEllPointTransition_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointTransition.{u} ℓ E n) := by
  unfold spEllPointTransition
  infer_instance

/-- The finite twist, regarded as an O_E,X-module through the quotient map.
Since mu is killed by ell^(n+1), B_X tensor_Z mu is precisely its extension
from (Z/ell^(n+1))_X to B_X.
Source: blueprint finite-level integral twist (blueprint: definition-tate-twists). -/
def spIntegralTwistLevel (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (Mod.comap (spEllReduction X ℓ E n)).obj
    ((Mod.free (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)).obj
      (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))

private theorem spFreeTensor_linear
    {C : Type*} [Category C] [MonoidalCategory C]
    {R B D : C} [MonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] (q : R ⟶ D) [IsMonHom q]
    (r : B ⟶ D) [IsMonHom r] (h : p ≫ r = q)
    {U V : C} (v : U ⟶ V) :
    ∃! f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
        (Mod.comap q).obj ((Mod.free D).obj V), f.hom = r ⊗ₘ v := by
  let f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
      (Mod.comap q).obj ((Mod.free D).obj V) := Mod.homMk (r ⊗ₘ v) (by
    change (p ▷ (B ⊗ U) ≫ (α_ B B U).inv ≫ MonObj.mul ▷ U) ≫ (r ⊗ₘ v) =
      R ◁ (r ⊗ₘ v) ≫ q ▷ (D ⊗ V) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V
    have hm : (p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r =
        (q ⊗ₘ r) ≫ MonObj.mul := by
      rw [IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h, Category.id_comp]
    calc
      _ = (α_ R B U).inv ≫ (((p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r) ⊗ₘ v) := by
        simp only [Category.assoc]
        rw [associator_inv_naturality_left_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (α_ R B U).inv ≫ (((q ⊗ₘ r) ≫ MonObj.mul) ⊗ₘ v) := by rw [hm]
      _ = (q ⊗ₘ (r ⊗ₘ v)) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V := by
        rw [associator_inv_naturality_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      _ = _ := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id])
  refine ⟨f, rfl, ?_⟩
  intro g hg
  exact Mod.hom_ext _ _ hg

set_option backward.isDefEq.respectTransparency false in
/-- The normalized transition is linear over O_E,X.
Source: blueprint u tensor a -> u^ell tensor a-bar (blueprint: definition-tate-twists).
Proof: reduce the scalar factor and apply the root power transition. Both commute
with restrictions. Reduction commutes with the O_E action, so the tensor map is
O_E-linear. The forgetful functor is faithful, giving uniqueness. -/
theorem spIntegralLevelTransition_existsUnique (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) :
    ∃! f : spIntegralTwistLevel X ℓ E (n + 1) ⟶ spIntegralTwistLevel X ℓ E n,
      f.hom = coefficientMap.{u} (spEllPointTransition ℓ E n) X ⊗ₘ
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) := by
  have hq : spEllReduction X ℓ E (n + 1) ≫
      coefficientMap.{u} (spEllPointTransition ℓ E n) X = spEllReduction X ℓ E n := by
    rw [← coefficientMap_comp]
    apply congrArg (fun f ↦ coefficientMap.{u} f X)
    unfold spEllPointReduction spEllPointTransition
    rw [← Functor.map_comp]
    rfl
  exact spFreeTensor_linear (spEllReduction X ℓ E (n + 1)) (spEllReduction X ℓ E n)
    (coefficientMap.{u} (spEllPointTransition ℓ E n) X) hq
    (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1))))

/-- The specified finite-level transition, with its reduction and Kummer factors.
Source: blueprint integral inverse system (blueprint: definition-tate-twists). -/
def spIntegralLevelTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spIntegralTwistLevel X ℓ E (n + 1) ⟶ spIntegralTwistLevel X ℓ E n :=
  (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose

/-- The positive finite-level twist system in O_E,X-modules.
Source: blueprint integral inverse system (blueprint: definition-tate-twists). -/
def spIntegralTwistSystem (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  Functor.ofOpSequence (spIntegralLevelTransition X ℓ E)

/-- O_E,X(1), the inverse limit with the pulled-back continuous integer coefficients.
Source: blueprint Tate twists, integral formula (blueprint: definition-tate-twists). -/
def spIntegralTwist (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  limit (spIntegralTwistSystem X ℓ E)

/-- E_X(1), extension of the integral twist along the continuous inclusion O_E -> E.
Source: blueprint Tate twists, rational formula (blueprint: definition-tate-twists). -/
def spRationalTwist (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X) :=
  (Mod.extendScalars.{u + 1, u + 2}
    (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (padicIntegersToPadicSubfield X ℓ E)).obj
    (spIntegralTwist X ℓ E)

end AlgebraicGeometry.ProEtale
