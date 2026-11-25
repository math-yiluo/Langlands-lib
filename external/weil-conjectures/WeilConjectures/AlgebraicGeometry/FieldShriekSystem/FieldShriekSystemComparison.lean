/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemFiniteLaws
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemMixed
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemCoherence
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemFiniteLaws
import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerSectionCoordinates
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemEvaluation
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.CategoryTheory.Integral.IntegralResidueMatePasting
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemTransitions
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageScalarCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Coherent compact-support comparison on coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: lem-sp-field-shriek-system-comparison).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard

/-- Invertibility on the recorded normalized full subcategory.
Source: blueprint (2), finite isomorphisms and conservativity
(blueprint: lem-sp-field-shriek-system-comparison). -/
structure InvertibilityLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  invertible : ∀ (E F : Index P) (h : E ≤ F)
    (M : SpTowerShriek.D P.coefficients.l E.val X), normalized P D E X M →
    IsIso ((comparison P D h c).app M)

/-- The complete system comparison assertion, retaining every clause.
Source: blueprint (2), all comparison clauses
(blueprint: lem-sp-field-shriek-system-comparison). -/
structure Laws (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    extends InvertibilityLaw P D c, MixedLaw P D c, CoherenceLaw P D c

/-- The specified natural isomorphism on the recorded normalized full subcategory.
Its forward morphism is literally the proper/open word, not an unspecified isomorphism.
Source: blueprint (2), b : C_Y P_A isomorphic to P_B C_X
(blueprint: lem-sp-field-shriek-system-comparison). -/
def iso (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (l : Laws P D c) {E F : Index P} (h : E ≤ F) :
    (normalized P D E X).ι ⋙
        (SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c ⋙
          (D.scalars E F h Y).T) ≅
      (normalized P D E X).ι ⋙
        ((D.scalars E F h X).T ⋙
          SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c) :=
  NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _ ((comparison P D h c).app M.obj)
      (l.invertible E F h M.obj M.property))
    (fun v ↦ (comparison P D h c).naturality v.hom)

end AlgebraicGeometry.ProEtale.FieldShriekSystem
