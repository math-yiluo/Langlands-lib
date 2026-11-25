/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicReductionEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicPointwiseAssembly
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors

/-! # Normalized Ext assembly with fixed reduction and cone data

Source: diagonal limit (3).
(blueprint: def-diagonal-cyclic-reduction-assembly-spec).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local instance 4000] cyclicCoefficientHasExt
  AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction
attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

/-- Literal normalized assembly after fixing the quotient and derived boundary.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-reduction-assembly-spec).
The normalization predicates, Ext classes, representative equations, completed
arrow, finite cycle equation and coefficient comparison remain arguments. -/
@[irreducible] def cyclicReductionAssemblySpec
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [eSys : HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (M : DiagonalCompletedReduction l (diagonalSurface Y)) : Prop :=
  cyclicFixedArrowAssemblySpec
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := (diagonalSurface Y)))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := (diagonalSurface Y)))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (eS := eSys) n
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p)
    (cyclicCompletedQuotient l (diagonalSurface Y) M n)
    (cyclicDiscreteRestriction l (diagonalSurface Y))
    (cyclicStrictBoundary l Y D) a b

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
