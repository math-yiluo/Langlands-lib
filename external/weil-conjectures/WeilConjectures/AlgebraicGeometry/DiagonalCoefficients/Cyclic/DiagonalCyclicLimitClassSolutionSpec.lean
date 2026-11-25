/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtRepresentative
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierClass
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicPointwiseAssembly
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicReductionEndpoints

/-! # The solution predicate for realized cyclic representatives

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-limit-class-solution-spec).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction
  cyclicSystemEvaluation cyclicStrictBoundary

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local instance 4000] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory diagonalCompletedSource

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
  cyclicEvaluationFunctor CyclicCartierFrame.reduce

/-- The universal solution for realized representatives of the supplied arrow.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-limit-class-solution-spec).
This names a literal equation predicate with no strict class or family selected. -/
@[irreducible] def cyclicLimitClassSolutionSpec
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y) : Prop :=
  cyclicRepresentativeSolution
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p) δ
    (DiagonalTrace.finiteCartierClass l Y hY n)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
