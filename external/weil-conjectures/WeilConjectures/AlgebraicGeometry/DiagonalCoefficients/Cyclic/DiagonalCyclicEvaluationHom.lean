/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEquations
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteEvaluationHom
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicRestrictedFrameClassEquation

/-! # Derived Hom representative of the explicit cyclic scalar reduction

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-evaluation-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
universe a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ d₀ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local instance 4000] cyclicCoefficientHasExt

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  geoCartierConstant geoCartierLine cartierRootsIso cartierEtaleKummerUnit
  cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary Functor.mapDerivedCategory shiftFunctor

attribute [local irreducible] cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

attribute [local irreducible] cyclicEvaluationSource cyclicEvaluationTarget

attribute [local semireducible] cyclicFiniteEvaluationHomEquation
  finiteRealizedEvaluationEquation

/-- The explicit representative of the realized cyclic scalar reduction.

Source: diagonal tower coefficient changes (1).
(blueprint: lem-diagonal-cyclic-evaluation-hom).

Proof: substitute Reference.delta, apply the exact-functor Ext-to-Hom formula,
then expand the two exact realizations and the scalar functor. Functoriality and
associativity give exactly the source, arrow and shifted target composites. -/
theorem cyclicEvaluation_hom
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (n : ℕ) (p : CyclicCartierFrame l Y n) :
    cyclicHomEquation l Y δ family reference n p := by
  unfold cyclicHomEquation
  rw [cyclicRestrictedFrameClass_eq]
  delta cyclicEvaluationSource cyclicEvaluationTarget cyclicEvaluationFunctor
  exact completedFunctorCalculation reference.eW.F
    (cyclicFiniteEvaluationFunctor l Y n p) 2 reference.sourceIso reference.eW.lineIso
    (cyclicFiniteEvaluationSource l Y n p) (cyclicFiniteEvaluationTarget l Y n p)
    δ family.zl.delta reference.delta
    (cyclicExtRepresentative ((p.reduce l Y n family.zl.delta).mapExactFunctor
      (diagonalFiniteToPadic l n (diagonalSurface Y))))
    (cyclicFiniteEvaluation_hom l Y n p family.zl.delta)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
