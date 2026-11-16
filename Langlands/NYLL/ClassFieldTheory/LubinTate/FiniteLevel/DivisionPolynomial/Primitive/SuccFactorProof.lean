/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 344, 2026-11-16: the proof of M339.019
(source lines 273–290) of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; Langlands.NYLL namespace
prefix, focused imports of the published target and successor proof,
an explicit fully applied statement target, an initial target unfolding,
and new module documentation. See the paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.SuccProof
import Mathlib.Tactic.Ring

/-!
# Successor factorization for standard Lubin--Tate polynomial iterates

This proves the published M339.019 target by expanding composition and
factoring out the preceding iterate in the polynomial ring.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The next compositional iterate is the current iterate times its primitive
quotient polynomial. -/
theorem standardLubinTatePolynomialIterate_succ_factor
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate_succ_factorStatement F π n := by
  unfold standardLubinTatePolynomialIterate_succ_factorStatement
  have hq : Nat.card F.residueField ≠ 0 :=
    ne_of_gt
      (Nat.zero_lt_one.trans
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
  rw [standardLubinTatePolynomialIterate_succ,
    standardLubinTatePolynomial,
    standardLubinTatePrimitivePolynomial]
  simp only [Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [← pow_sub_one_mul hq]
  ring

end Langlands.NYLL.LubinTate

end
