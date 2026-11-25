/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEvaluationCalculation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteClassTransport

/-! # Transport of a single normalized finite evaluation

Source: the finite reduction comparisons of the diagonal limit theorem and
diagonal coefficient changes (1).
(blueprint: lem-diagonal-cyclic-evaluation-transport).
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

attribute [local irreducible] CyclicCartierFrame.reduce

attribute [local semireducible] cyclicTransportEquation

/-- The cyclic scalar reduction and the prescribed finite residue class agree
only after restriction to discrete integral coefficients. The frame is supplied;
no frame is constructed, and no equality before restriction is asserted.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.proof.md, finite reduction comparisons in (3), and
sk-prop-diagonal-tower-coefficients.proof.md (1).
(blueprint: lem-diagonal-cyclic-evaluation-transport).

Proof: unpack IsDiagonalLimit into its strict class c, derived endpoint
isomorphisms a,b, ordinary root system, finite endpoint normalizations, and the
complete normalized-limit witnesses L,M,s0,t0. Apply the last ArrowCompatibility
clause to delta, its whole-limit equation, and n. This gives two finite endpoint
comparisons, their normalized quotient-unit squares and the finite arrow equation.
The source cone and finite source normalizations identify the source square with
the full supported scalar unit. The root cone and finite target normalizations
identify the target square with the actual n-th root projection. The uniqueness
of normalized integral root maps identifies the integral roots of Reference and p.
Completed realization unit normalization and the normalized condensed Z_l quotient
identify the coefficient map with continuous PadicInt.toZModPow. Uniqueness of
scalar adjoints identifies these units with p.supported and p.line, including its
finite line endpoint. Substitute the finite arrow equation and the equation for
c.hom. Exact-single and shift naturality transport evaluation of c by the finite
source and target isomorphisms. Ext.homEquiv gives the equality after restriction.
Reference.delta identifies the realized completed arrow with family.zl.delta.
Finally the n-th finite-cycle equation identifies this evaluation with the
restriction of cartierResidueReducedPro. This comparison performs no construction
of a cyclic frame, no cancellation of restriction, and no identification of the
residue class with the positive canonical Cartier class. It applies at n=0 and
to the empty scheme. -/
theorem diagonalCyclicEvaluation_transport
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (n : ℕ)
    (p : CyclicCartierFrame l Y n)
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ) :
    (p.reduce l Y n family.zl.delta).mapExactFunctor
        (diagonalFiniteToPadic l n (diagonalSurface Y)) =
      (cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
        (diagonalImmersion Y) (diagonalImmersion_cartier Y)
        (diagonalSurface_power_unit l Y hY n)).mapExactFunctor
          (diagonalFiniteToPadic l n (diagonalSurface Y)) := by
  exact finiteCyclicTransport_to_transportEquation l Y hY family n p
    (diagonalCyclicEvaluation_calculation l Y hY D δ family reference n p hδ)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
