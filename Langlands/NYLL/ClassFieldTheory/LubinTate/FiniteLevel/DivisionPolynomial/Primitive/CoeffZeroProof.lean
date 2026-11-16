/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 661, 2026-11-16: extract the proof of M339.018
(source lines 261–271) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL, state the theorem using the fully applied published
Statement, and replace the upstream imports by focused published modules.
Expose the imported iterate proposition as an equality for simplification.
The simp attribute and the source proof route are retained.
See the paired Markdown for the complete modification record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.EvalZeroProof

/-!
# Constant coefficient of the primitive Lubin--Tate polynomial

This module proves the published M339.018 target for every valuation-ring
element and natural level.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.018: the constant coefficient of the primitive quotient
polynomial is `π`. -/
@[simp]
theorem standardLubinTatePrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomial_coeff_zeroStatement F π n := by
  change (standardLubinTatePrimitivePolynomial F π n).coeff 0 = π
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hzero : (standardLubinTatePolynomialIterate F π n).eval 0 = 0 :=
    standardLubinTatePolynomialIterate_eval_zero F π n
  simp [standardLubinTatePrimitivePolynomial, hzero,
    ne_of_gt
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))]

end Langlands.NYLL.LubinTate

end
