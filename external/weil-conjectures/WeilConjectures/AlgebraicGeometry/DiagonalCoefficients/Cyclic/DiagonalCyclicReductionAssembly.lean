/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicReductionAssemblySpec
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFrameAssembly

/-! # Normalized Ext assembly with fixed reduction and cone data

Source: diagonal limit (3).
(blueprint: lem-diagonal-cyclic-reduction-assembly).
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
  cyclicFrameAssemblySpec cyclicPointwiseAssemblySpec
attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

/-- The fixed normalized reduction contract follows from the proved frame assembly.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-reduction-assembly).
Proof: specialize the pointwise assembly contract to the supplied quotient,
restriction and strict-system endpoints, leaving the normalization predicates variable. -/
theorem cyclicExtAssembly_reduction
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
    (M : DiagonalCompletedReduction l (diagonalSurface Y)) :
    cyclicReductionAssemblySpec l Y eW sourceIso n p D H a b M := by
  unfold cyclicReductionAssemblySpec
  exact cyclicFixedArrowAssembly_of_pointwise
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (eS := eSys) n
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p)
    (cyclicCompletedQuotient l (diagonalSurface Y) M n)
    (cyclicDiscreteRestriction l (diagonalSurface Y))
    (cyclicStrictBoundary l Y D) a b
    (cyclicExtAssembly_frame l Y n eW sourceIso p)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
