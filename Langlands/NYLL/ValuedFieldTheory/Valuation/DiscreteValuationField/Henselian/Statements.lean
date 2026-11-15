/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Definitions

/-!
# Targets: idempotent lifting and Henselian discrete valuation fields

Modified by Worker 5264, 15 November 2026: state the source theorems M104.001
`idempotentPolynomial_monic`, M104.002
`idempotentPolynomial_eval_mem_of_quotient_idempotent`, M104.003
`idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent`, M104.004
`exists_idempotent_lift_of_surjective_henselianRing_ker`, M104.013
`HenselianDVF.valuationSubring_isDiscreteValuationRing` and M104.015
`HenselianDVF.maximalIdeal_ne_bot` of
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, omit the proofs and the rest of the source file, import the
published `Henselian.Definitions` module instead of the source imports, and
turn off the unused-variable linter for the hypotheses `ha0` of M104.002 and
M104.003 and `hf`, `he` of M104.004, which the propositions do not mention.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ValuationTheory

noncomputable section

universe u v

namespace DiscreteValuationField

/-- Target: the idempotent polynomial `X^2 - X` is monic in every nontrivial
coefficient ring. -/
def idempotentPolynomial_monicStatement
    {R : Type*} [CommRing R] [Nontrivial R] : Prop :=
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic

set_option linter.unusedVariables false in
/-- Target: a quotient idempotent is an approximate root of `X^2 - X`. -/
def idempotentPolynomial_eval_mem_of_quotient_idempotentStatement
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) : Prop :=
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0 ∈ I

set_option linter.unusedVariables false in
/-- Target: at a quotient idempotent, the derivative of `X^2 - X` is a unit in
the quotient. -/
def idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) : Prop :=
    IsUnit
      (Ideal.Quotient.mk I
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0))

set_option linter.unusedVariables false in
/-- Target: idempotents lift along a surjective ring map whose kernel is a
Henselian ideal.

This is the `X^2 - X` simple-root form of Hensel's lemma.  At an idempotent,
the derivative `2X - 1` is a unit because its square is `1`. -/
def exists_idempotent_lift_of_surjective_henselianRing_kerStatement
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) : Prop :=
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- Target: the valuation subring of the henselian model is a discrete
valuation ring. -/
def valuationSubring_isDiscreteValuationRingStatement
    (F : HenselianDVF.{u, v} K) : Prop :=
    IsDiscreteValuationRing F.valuationSubring

/-- Target: the maximal ideal of a Henselian DVF valuation ring is nonzero. -/
def maximalIdeal_ne_botStatement (F : HenselianDVF.{u, v} K) : Prop :=
    F.maximalIdeal ≠ ⊥

end HenselianDVF

end DiscreteValuationField

end

end Langlands.NYLL.ValuationTheory
