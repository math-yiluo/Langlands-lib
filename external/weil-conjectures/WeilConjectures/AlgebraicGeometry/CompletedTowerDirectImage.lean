/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedTowerPullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.FourCorners
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
import WeilConjectures.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Total direct image of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1276;
Stacks Project, Tag 099N (blueprint: proposition-proper-base-change-complete-integral--1).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient direct-image structure map adjoint to c_f.
Source: blueprint order 1276 (blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedCoefficientDirectImageMap :
    pbcAdicCompletion Y d ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion X d) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (pbcAdicCompletion Y d) ≫
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (completedCoefficientMap f d)

@[instance]
theorem completedEvaluation_preservesKInjective (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
      (op n)).PreservesKInjectiveComplexes := by
  constructor
  intro I hI
  exact tower_evaluation_isKInjective (pbcModules T R) I (op n)

end AlgebraicGeometry.Scheme
