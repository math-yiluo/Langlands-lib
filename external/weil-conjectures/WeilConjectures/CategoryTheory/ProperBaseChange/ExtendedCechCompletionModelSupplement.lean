/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.ExtendedCechReflectorCore
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteUnitCriterion
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomTensorNaturality
import WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic.Basic
import WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import WeilConjectures.Algebra.Homology.KFlatComparison
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexDescentData
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.AugmentedComplexGluing
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexIdealDescent
import WeilConjectures.AlgebraicGeometry.RingFamilyLocallyEqualModels
import WeilConjectures.CategoryTheory.ModuleSheafificationLocalIso
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.AlgebraicGeometry.RingFamilyRestriction
import WeilConjectures.CategoryTheory.ModuleSheafificationRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.RingedGeneratingListsLocalEquality
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexCechComparison
import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementRelations
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.RingComplexGodementCech
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparison
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonAlpha
import WeilConjectures.AlgebraicGeometry.FlasqueAlternatingCechRowAugmentation
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import WeilConjectures.Topology.Sheaves.CechFlasque
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation
import WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonBeta
import WeilConjectures.AlgebraicGeometry.FiniteOrderedCechCoefficientMap
import WeilConjectures.AlgebraicGeometry.FiniteOrderedCechTotalMap
import WeilConjectures.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementStalkContraction
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechCoordinates
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechConstruction
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechSectionCoordinates
import WeilConjectures.AlgebraicGeometry.RingComplexGodementAffineSections
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.GlobalSectionRingFamilyBaseChange
import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionTransportSupplement
import WeilConjectures.AlgebraicGeometry.RingComplexCechBaseChange
import WeilConjectures.AlgebraicGeometry.RingComplexCechScalarModel
import WeilConjectures.AlgebraicGeometry.RingComplexOrderedScalarIso
import WeilConjectures.AlgebraicGeometry.RingComplexScalarAugmentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.RingComplexCechAugmentationHom
import WeilConjectures.AlgebraicGeometry.RingComplexCechLocalizedOrthogonality
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.AlgebraicGeometry.RingComplexCechCohomologyPowerTorsion
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.AlgebraicGeometry.PowerTorsionLocalizedShiftHom
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.AlgebraicGeometry.RingComplexCechConeFiltration
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarCechModel
import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.GlobalSectionOrderedCechTensor
import WeilConjectures.AlgebraicGeometry.GlobalSectionTensorBaseChange
import WeilConjectures.AlgebraicGeometry.RingTensorCechCoordinates
import WeilConjectures.AlgebraicGeometry.RingCechCoordinateTensorStep
import WeilConjectures.AlgebraicGeometry.RingLocalizationTensorBlocks
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Prod
import WeilConjectures.AlgebraicGeometry.RingPointTensorComparison
import WeilConjectures.AlgebraicGeometry.RingCechAlgebraicConeCoordinates
import WeilConjectures.AlgebraicGeometry.RingCechConeLinearEquiv
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Order.Fin.SuccAboveOrderIso
import Mathlib.Order.Fin.Tuple
import WeilConjectures.AlgebraicGeometry.RingCechConeDifferential
import WeilConjectures.AlgebraicGeometry.GlobalSectionComplexMonoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.GlobalSectionModuleMonoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.AlgebraicGeometry.GlobalSectionModuleOplaxNormalized
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ScalarExtensionMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionLocalizationFactor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.RingComplexGodementFunctorial
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.RingComplexGodementModelMapsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel

/-!
# Global extended Cech model and its derived completion unit

Source: Stacks Project, algebraization.tex, Tags 099E and 099F
(blueprint: lem-weil-pbc-extended-cech-completion-model).
-/

@[expose] public section
set_option linter.privateModule false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

private theorem compose_three_squares {D : Type*} [Category D]
    {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : D}
    {f : A₁ ⟶ A₂} {g : B₁ ⟶ B₂} {h : C₁ ⟶ C₂} {k : D₁ ⟶ D₂}
    {a : A₁ ⟶ B₁} {a' : A₂ ⟶ B₂} {b : B₁ ⟶ C₁} {b' : B₂ ⟶ C₂}
    {c : C₁ ⟶ D₁} {c' : C₂ ⟶ D₂}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) (hc : h ≫ c' = c ≫ k) :
    f ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ k := by
  calc
    _ = (f ≫ a') ≫ b' ≫ c' := by simp only [Category.assoc]
    _ = a ≫ (g ≫ b') ≫ c' := by rw [ha]; simp only [Category.assoc]
    _ = a ≫ b ≫ (h ≫ c') := by rw [hb]; simp only [Category.assoc]
    _ = _ := by rw [hc]; simp only [Category.assoc]

-- Descending evaluation compares several expanded product-localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem unit_isIso_of_complete_universal
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E)
    (hc : ∀ E, P (F.obj E))
    (hu : ∀ E L, P L → Function.Bijective (fun h : F.obj E ⟶ L ↦ η E ≫ h))
    (E : D) (hE : P E) : IsIso (η E) := by
  obtain ⟨r, hr⟩ := (hu E E hE).2 (𝟙 E)
  have hs : r ≫ η E = 𝟙 (F.obj E) := by
    apply (hu E (F.obj E) (hc E)).1
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hs⟩⟩

end CategoryTheory
