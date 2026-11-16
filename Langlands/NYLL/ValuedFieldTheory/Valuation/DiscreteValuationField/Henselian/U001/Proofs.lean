/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 740, 16 November 2026: extract only the proof of M104.001
`idempotentPolynomial_monic` from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean
(lines 27–32) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published Henselian.Statements module, state
the theorem as its `idempotentPolynomial_monicStatement` and open it with
`unfold` before the unchanged source tactic proof. The noncomputable section
and the unused universes u v are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Statements

/-!
# The idempotent polynomial is monic (NYLL M104.001)

In every nontrivial commutative ring, `X ^ 2 - X` is monic.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- The idempotent polynomial `X^2 - X` is monic in every nontrivial
coefficient ring. -/
theorem idempotentPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R] :
    idempotentPolynomial_monicStatement (R := R) := by
  unfold idempotentPolynomial_monicStatement
  exact Polynomial.monic_X_pow_sub (by
    rw [Polynomial.degree_X]
    norm_num)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
