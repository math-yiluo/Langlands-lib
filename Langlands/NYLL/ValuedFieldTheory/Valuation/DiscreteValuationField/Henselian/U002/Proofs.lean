/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.002
`idempotentPolynomial_eval_mem_of_quotient_idempotent` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 35–43) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module, state
the theorem as its
`idempotentPolynomial_eval_mem_of_quotient_idempotentStatement` applied to
the source binders and open it with `unfold` before the unchanged source
tactic proof. The noncomputable section and the unused universes u v are
omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# A quotient idempotent is an approximate root of `X ^ 2 - X` (NYLL M104.002)

If the class of `a0` modulo an ideal `I` is idempotent, then
`a0 ^ 2 - a0 ∈ I`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- A quotient idempotent is an approximate root of `X^2 - X`. -/
theorem idempotentPolynomial_eval_mem_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    idempotentPolynomial_eval_mem_of_quotient_idempotentStatement a0 ha0 := by
  unfold idempotentPolynomial_eval_mem_of_quotient_idempotentStatement
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0) = 0
  simpa [pow_two] using sub_eq_zero.mpr ha0.eq

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
