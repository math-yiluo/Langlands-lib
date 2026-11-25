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
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteClassTransportEquation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEvaluationHom
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicLimitClassSolution

/-! # Calculation of cyclic transport with a named equation type

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-evaluation-calculation).
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

attribute [local semireducible] cyclicHomEquation finiteCyclicTransportEquation
  cyclicLimitClassSolutionSpec cyclicRepresentativeSolution cyclicNormalizedLimitEquation
  DiagonalTrace.SupportedSourceConeNormalization

/-- The normalized limit presentation supplies the finite transport input.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-evaluation-calculation).
Proof: extract the strict class and normalized cone witnesses, then apply
the proved normalized transport calculation. -/
theorem diagonalCyclicEvaluation_calculation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [eSys : HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (n : ℕ)
    (p : CyclicCartierFrame l Y n)
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ) :
    finiteCyclicTransportEquation l Y hY family n p := by
  rcases hδ with ⟨H, roots, a, b, c, data⟩
  obtain ⟨L, M, s₀, t₀, hnormal⟩ := data.2.2.2
  exact cyclicExtAssembly_limitClass l Y hY D δ
    reference.eP reference.eW reference.sourceIso n p
    H roots a b c L M s₀ t₀ data.2.1 data.2.2.1 hnormal reference.source_normalization
    _ (cyclicEvaluation_hom l Y δ family reference n p)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
