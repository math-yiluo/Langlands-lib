/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicReductionAssemblySpec

/-! # Calculation of cyclic transport with a named equation type

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-endpoint-assembly-spec).
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

attribute [local semireducible] cyclicReductionAssemblySpec cyclicArrowAssemblySpec

attribute [local semireducible] cyclicFixedArrowAssemblySpec

/-- Literal class transport contract after the two endpoint squares are known.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-endpoint-assembly-spec).
This names a universal equation; the following module proves it from comparison. -/
@[irreducible] def cyclicEndpointAssemblySpec
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [eSys : HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (n : ℕ)
    (p : CyclicCartierFrame l Y n)
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
      (M : DiagonalCompletedReduction l (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
 : Prop :=
  let F := cyclicDiscreteRestriction l (diagonalSurface Y)
  let Rn := cyclicCompletedQuotient l (diagonalSurface Y) M n
  let K := D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))
  let J := D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
    (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)
  cyclicResolvedAssemblySpec
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := (diagonalSurface Y)))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := (diagonalSurface Y)))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (eS := eSys) n
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p) Rn F
    (cyclicStrictBoundary l Y D) a b
    (DiagonalSourceNormalization l Y D.ordinary n)
    (DiagonalTrace.FiniteRootNormalization l Y hY H roots n)
    (fun sa ↦ F.map ((M.unit n).app (diagonalCompletedDomain l Y)) ≫ sa.hom =
      diagonalSourceLimitMap l Y D a L s₀ ≫ (L.projection n).app K)
    (fun ta ↦ F.map ((M.unit n).app (diagonalCompletedCodomain l Y)) ≫ ta.hom =
      diagonalTargetLimitMap l Y D H b L t₀ ≫ (L.projection n).app J)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
