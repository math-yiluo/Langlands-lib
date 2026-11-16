/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.003
`idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 47–83) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module, state
the theorem as its
`idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement`
applied to the source binders and open it with `unfold` before the unchanged
source tactic proof. The noncomputable section and the unused universes u v
are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# The derivative of `X ^ 2 - X` at a quotient idempotent is a unit (NYLL M104.003)

If the class `e` of `a0` modulo an ideal `I` is idempotent, then the class of
`2 * a0 - 1` is a unit of `R ⧸ I`, being its own inverse:
`(2e - 1) ^ 2 = 1 + 4 (e ^ 2 - e) = 1`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- At a quotient idempotent, the derivative of `X^2 - X` is a unit in the
quotient. -/
theorem idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement
      a0 ha0 := by
  unfold idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement
  rw [isUnit_iff_exists]
  refine
    ⟨Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0),
      ?_, ?_⟩
  · simp only [pow_two, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, mul_one, Polynomial.eval_sub,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub, map_add,
      map_one]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring
  · simp only [pow_two, Polynomial.derivative_mul,
      Polynomial.derivative_X, one_mul, mul_one, Polynomial.eval_sub,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, map_sub, map_add,
      map_one]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
