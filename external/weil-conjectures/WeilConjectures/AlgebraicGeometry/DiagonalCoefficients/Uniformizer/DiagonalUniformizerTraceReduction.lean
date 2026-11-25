/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteArrowEquations
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteTracePresentation.DiagonalFiniteTraceChernCriterion
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerTraceChernDegree

/-! # The finite image of the completed projective-line trace

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-uniformizer-trace-reduction).
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
  QuotientLineRealization

/-- The scalar reduction of the completed projective-line trace, for supplied
finite coefficient models, a fully normalized direct-image square, and a supplied
positive unit/Chern splitting. This states no class comparison or model existence.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), reduction of the trace;
and sk-prop-diagonal-tower/_section.md, the trace and integration identities.
(blueprint: lem-diagonal-uniformizer-trace-reduction).

Proof: The reference identifies family.zl.traceq with the completed trace whose
projective-line model is the identity. By its definition this is the inverse of
the completed positive unit/Chern splitting followed by constant projection.
Reduce that entire splitting modulo l^(n+1) and extend coefficients to A. The
unit reduces to the canonical constant unit by reference.eY.unit_normalization;
the Kummer Chern component reduces to the canonical finite Chern component by
coefficient naturality. The root projection equation in lineP identifies the
positive finite Tate endpoint. Therefore the reduced splitting has hom exactly
geoP1TwistedMap and equals splitting by hsplitting and isomorphism extensionality.
Functors preserve inverses, so its inverse followed by constant projection is
geoP1Trace. Use family.toIntegral E and scalar.q.trace to identify the scalar
image with d.traceq. The reference and finite q_square comparisons agree after
these reductions: their ordinary squares have the specified underlying maps,
and uniqueness of right derivation with its full universal unit fixes the
derived square. The hcanonical equation identifies its final model with the
canonical geoP1Pushforward. These substitutions give the asserted trace equation.
No use of the diagonal arrow or of detection of derived arrows by finite levels
is made. The argument applies at n=0 as well as at every higher positive power. -/
theorem diagonalUniformizer_traceReduction
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    [hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))]
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family.integral E) d)
    (eY : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y)
    (eP : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (lineP : QuotientLineRealization l E π n n hA (ProjectiveLine Y) eP)
    (presentation : FiniteTracePresentation
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow
      (quotientLine l E π n) d eY eP) :
    FinitePresentedTraceEquation
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hYpow
      (quotientLine l E π n) d eY eP (lineP.iso l) presentation := by
  apply finitePresentedTraceEquation_of_chern
  exact diagonalUniformizer_traceChernDegree l Y family.zl E π hπ n
    (family.integral E) (family.toIntegral E) reference.tq reference.eY reference.eP
    reference.q_model reference.q_square reference.q_trace
    hA hYpow d scalar eY eP lineP presentation

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
