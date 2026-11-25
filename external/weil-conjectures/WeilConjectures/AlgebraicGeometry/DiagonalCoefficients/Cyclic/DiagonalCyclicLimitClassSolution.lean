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
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicNormalizedLimitEquation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEndpointAssembly
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicLimitClassSolutionSpec

/-! # Calculation of cyclic transport with a named equation type

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-limit-class-solution).
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

attribute [local semireducible] cyclicExtRepresentative

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

attribute [local semireducible] cyclicNormalizedLimitEquation
  cyclicReductionAssemblySpec cyclicArrowAssemblySpec

attribute [local semireducible] DiagonalTrace.FiniteCartierNormalization
  cyclicFixedArrowAssemblySpec cyclicEndpointAssemblySpec cyclicResolvedAssemblySpec

/-- Strict class and cone data determine every realized representative.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-limit-class-solution).
Proof: specialize endpoint assembly, apply finite normalization and arrow
compatibility at n, and leave the realized class and its representative arbitrary. -/
theorem cyclicExtAssembly_limitClass
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [eSys : HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (eP : CompletedRealization l (ProjectiveLine Y))
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
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
      (M : DiagonalCompletedReduction l (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (hc : c.hom = a.inv ≫ cyclicStrictBoundary l Y D ≫ b.hom)
    (hfinite : DiagonalTrace.FiniteCartierNormalization l Y hY D.ordinary H roots c)
    (hnormal : cyclicNormalizedLimitEquation l Y D δ H roots a b L M s₀ t₀)
    (source_normalization :
      HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ sourceIso.hom.hom)
        ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (eP.underlying.inv.app (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
            eP.unitIso.hom.hom))) :
    cyclicLimitClassSolutionSpec l Y hY eW sourceIso n p δ := by
  unfold cyclicLimitClassSolutionSpec
  exact cyclicRepresentativeSolution_of_resolved
    (dA := DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (dS := DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y))
    (eA := cyclicCoefficientHasExt l (diagonalSurface Y))
    (eS := eSys) n
    (cyclicEvaluationFunctor l Y n eW p)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    (cyclicEvaluationTarget l Y n eW p)
    (cyclicCompletedQuotient l (diagonalSurface Y) M n)
    (cyclicDiscreteRestriction l (diagonalSurface Y))
    (cyclicStrictBoundary l Y D) a b _ _ _ _
    (cyclicExtAssembly_endpoints l Y hY D eP eW sourceIso
      n p H roots a b L M s₀ t₀ source_normalization hnormal.1.1 hnormal.1.2.1)
    δ c hc (DiagonalTrace.finiteCartierClass l Y hY n)
    (hfinite n) (hnormal.1.2.2.2.2.2.2.2 δ hnormal.2 n)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
