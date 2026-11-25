/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFrameAssemblySpec
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicExtDiagonalAssembly

/-! # Ext assembly contract for a supplied cyclic frame

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-frame-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

attribute [local semireducible] cyclicEvaluationAssemblySpec

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

/-- Proved Ext assembly for a supplied cyclic frame, before geometric classes are inserted.
Source: coefficient changes (1) (blueprint: lem-diagonal-cyclic-frame-assembly).
Proof: specialize diagonal evaluation assembly to the frame's actual quotient
functor, source, target and representative endpoint maps. The remaining data stay abstract. -/
theorem cyclicExtAssembly_frame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [eSys : HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (p : CyclicCartierFrame l Y n) : cyclicFrameAssemblySpec l Y n eW sourceIso p := by
  unfold cyclicFrameAssemblySpec
  exact cyclicPointwiseAssembly_of_spec
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (eS := eSys) n
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p)
    (cyclicExtAssembly_diagonal l (diagonalSurface Y) n)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
