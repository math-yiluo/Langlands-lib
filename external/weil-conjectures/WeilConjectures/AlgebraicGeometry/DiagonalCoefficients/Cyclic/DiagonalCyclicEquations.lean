/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicRestrictedFrameClass
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicReductionEndpoints

/-! # Literal proposition wrappers for cyclic transport equations

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
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
  cyclicEvaluationFunctor CyclicCartierFrame.reduce

/-- The equation for the derived representative, with the original endpoints.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-equations). -/
@[irreducible] def cyclicHomEquation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (n : ℕ) (p : CyclicCartierFrame l Y n) : Prop :=
    (show
      (DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
          ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))) ⟶
        ((DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
          ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
            (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
              (cartierResidue_cast l (n + 1)) (diagonalSurface Y))))⟦(2 : ℤ)⟧
      from cyclicExtRepresentative (cyclicRestrictedFrameClass l Y family n p)) =
      cyclicEvaluationSource l Y n reference.eW reference.sourceIso p ≫
        (cyclicEvaluationFunctor l Y n reference.eW p).map δ ≫
          cyclicEvaluationTarget l Y n reference.eW p

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
