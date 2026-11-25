/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotients
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerFiniteModels
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerCartierReduction
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerTraceReduction
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteTracePresentation

/-! # Finite normalization of an already reduced diagonal diagram

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-uniformizer-finite-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization FiniteDiagonalComparison

/-- Identify a supplied scalar-compatible quotient diagram with the positive finite
Cartier class and trace, at the fixed annihilating exponent. No quotient diagram or
scalar compatibility is constructed by this statement.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), finite reductions of
classes and traces. (blueprint: lem-diagonal-uniformizer-finite-normalization).

Proof: The finite discrete quotient ring has its canonical unital coefficient
comparison with the constant ring sheaf. Transport internal modules through this
ring comparison and the equivalence with sheaves of ordinary modules. This gives
exact realizations on Y, P and W, preserving the underlying sheaves and the unit.
The integral root-limit projection at n, followed by the coefficient reduction,
factors through the roots killed by l^(n+1), since hA kills this exponent. The
finite-root isomorphisms, normalized by the kernel inclusions into units, identify
the resulting reduced lines with the positive finite Tate lines. This gives lineP
and lineW, with exactly the root equations of QuotientLineRealization.

Use reference.delta to express family.zl.delta as the completed diagonal class.
The whole-system limit normalization hδ and hcompletion identify its reduction
modulo l^(n+1) with the canonical finite positive Cartier boundary. Extend from
Z/l^(n+1) to the quotient ring using Cartier scalar compatibility. Scalar
associativity, family.toIntegral and scalar.delta identify that boundary with
d.delta under the preceding source and line comparisons. For the trace, the
reference's full completed trace comparisons identify family.zl.traceq with the
inverse positive unit/Chern splitting followed by its constant projection. Apply
the same reduction and finite scalar extension. The canonical unit and the
Kummer Chern arrow reduce to their finite counterparts, so the splitting reduces
to geoP1TwistedMap and its inverse reduces to its inverse. The full right-derived
units fix the ordinary and derived realization/direct-image squares; scalar.q.trace
therefore gives the asserted equation for d.traceq. Assemble these comparisons
into FiniteDiagonalComparison. The argument uses the full normalized completed
arrow, not an assertion that separate reductions detect arbitrary derived arrows.
At n = 0 the exponent remains l; ramification changes the quotient but neither
the fixed annihilation nor the coefficient-naturality argument. -/
theorem diagonalUniformizer_finiteNormalization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (reference : Reference l Y δ family)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (hfinite : Finite (ULift.{u + 1} (completedResidue l E π n)))
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (hWpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (rootsP : FiniteRoots (ProjectiveLine Y) (l ^ (n + 1)))
    (rootsW : FiniteRoots (diagonalSurface Y) (l ^ (n + 1)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family.integral E) d) :
    ∃ (eY : FiniteRealization
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        (ULift.{u + 1} (completedResidue l E π n)) Y)
      (eP : FiniteRealization
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
      (eW : FiniteRealization
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        (ULift.{u + 1} (completedResidue l E π n)) (diagonalSurface Y))
      (lineP : QuotientLineRealization l E π n n hA (ProjectiveLine Y) eP)
      (lineW : QuotientLineRealization l E π n n hA (diagonalSurface Y) eW),
      FiniteDiagonalComparison
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
        (ULift.{u + 1} (completedResidue l E π n)) (hfinite := hfinite)
        (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow hWpow
        (quotientLine l E π n) d eY eP eW (lineP.iso l) (lineW.iso l) := by
  let B := completedResidue l E π n
  let A := ULift.{u + 1} B
  let R := Profinite.continuousMapRingObj.{u} B
  let := hfinite
  -- Direct elimination avoids reducing the large conclusion for each model witness.
  refine (diagonalUniformizer_finiteModels l Y hY E π hπ n hA hYpow hWpow
    rootsP rootsW).elim fun eY heY ↦ heY.elim fun eP heP ↦ heP.elim fun eW heW ↦
      heW.elim fun lineP hlineP ↦ hlineP.elim fun lineW hlineW ↦ ?_
  refine hlineW.1.elim fun sourceComparison ↦
    hlineW.2.elim fun ordinarySquare ↦ ?_
  refine (finiteTracePresentation_exists
    R A l (Fact.out : l.Prime)
    (n + 1) (Nat.succ_pos n) hA Y hYpow (quotientLine l E π n) d eY eP
    ordinarySquare).elim fun presentation ↦ ?_
  refine ⟨eY, eP, eW, lineP, lineW, ?_⟩
  apply finiteDiagonalComparison_of_equations
    R A
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow hWpow
    (quotientLine l E π n) d eY eP eW (lineP.iso l) (lineW.iso l)
    sourceComparison presentation
  · exact diagonalUniformizer_cartierReduction l Y hY D hcompletion hsystem δ hδ
      family reference E π hπ n hA hYpow hWpow d scalar
      eP eW lineW sourceComparison
  · exact diagonalUniformizer_traceReduction l Y δ family reference E π hπ n
      hA hYpow d scalar eY eP lineP presentation

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
