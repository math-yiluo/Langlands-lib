/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceConeNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteEvaluation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteRootNormalization

/-! # Natural cyclic quotient comparison with normalized source and root endpoints

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-evaluation-endpoints).
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

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

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

/-- The scalar quotient, realized as discrete integral modules. This functor is
independent of a diagonal class. Source: coefficient changes (1)
(blueprint: def-diagonal-cyclic-evaluation-endpoints). -/
def cyclicEvaluationFunctor (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    DerivedCategory (DiagonalCompleted l (diagonalSurface Y)) ⥤
      DerivedCategory (DiagonalMod l (diagonalSurface Y)) :=
  eW.F.mapDerivedCategory ⋙ cyclicFiniteEvaluationFunctor l Y n p

/-- The inverse supported-source comparison for the composite quotient functor.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-evaluation-endpoints). -/
def cyclicEvaluationSource (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (p : CyclicCartierFrame l Y n) :
    (DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (diagonalImmersion Y)).obj
              (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))) ⟶
      (cyclicEvaluationFunctor l Y n eW p).obj (diagonalCompletedDomain l Y) :=
  completedFunctorSource eW.F (cyclicFiniteEvaluationFunctor l Y n p) sourceIso
    (cyclicFiniteEvaluationSource l Y n p)

/-- The root comparison for the composite quotient functor, including its shift.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-evaluation-endpoints). -/
def cyclicEvaluationTarget (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    (cyclicEvaluationFunctor l Y n eW p).obj (diagonalCompletedCodomain l Y) ⟶
      ((DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) (diagonalSurface Y))))⟦(2 : ℤ)⟧ :=
  completedFunctorTarget eW.F (cyclicFiniteEvaluationFunctor l Y n p) 2 eW.lineIso
    (cyclicFiniteEvaluationTarget l Y n p)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
