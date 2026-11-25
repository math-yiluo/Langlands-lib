/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.FourCorners
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
public import WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
public import WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
public import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
public import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
public import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
public import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
public import WeilConjectures.CategoryTheory.TowerSplitEnvelope
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.RingTheory.FactorsThroughLocalization
public import WeilConjectures.RingTheory.FilteredColimitOfFactorization
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # Scalar pullback square coherence

Source: Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapHomotopyCategory
  AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private instance module_tensor_two
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B : GradedObject ℤ (Modules R T)) : A.HasTensor B := by
  intro j
  infer_instance

private instance module_tensor_four
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C E : GradedObject ℤ (Modules R T)) :
    GradedObject.HasTensor₄ObjExt A B C E := by
  intro i j
  infer_instance

private instance module_tensor_left
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

private instance module_tensor_right
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

private instance module_kflat_derivable
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure
      (HomotopyCategory.quasiIso (Modules R T) (.up ℤ)).localizerMorphismKFlat := by
  infer_instance

private instance extension_kflat (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u}) :
    (extension φ T).PreservesKFlatQuasiIso := by
  exact Mod.preservesKFlatQuasiIso (coefficientMap φ T)

/-- The canonical geometric compositor with the scalar interface exposed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackComposition
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    L R (h ≫ k) ≅ L R k ⋙ L R h := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarComp R h k

/-- The canonical geometric pullback square with the scalar interface exposed.
Source: Stacks 07A7 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullbackSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    L R c ⋙ L R f' ≅ L R f ⋙ L R a :=
  (scalarPullbackComposition R f' c).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ L R h) sq.toCommSq.w.symm) ≪≫
    scalarPullbackComposition R a f

-- Specializing the categorical lemma searches instances on categories of module objects.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStar Mod.extendScalars
  CondensedRing.upperStarComp CondensedRing.pullIso
  scalarCounit pullCounit

end AlgebraicGeometry.ProEtale.QuotientChange
