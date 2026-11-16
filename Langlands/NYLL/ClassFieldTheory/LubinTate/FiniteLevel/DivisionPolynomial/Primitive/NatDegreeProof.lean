/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 774, 2026-11-16: extract the proof of M339.016 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify the
namespace with Langlands.NYLL; state the theorem using the published
fully applied target; inline the degree calculations of M339.006 and
M339.011 as local facts; replace the imports by the published target and
Mathlib polynomial degree lemmas; drop unused scoped opens; replace the
module documentation. See the paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Natural degree of the primitive Lubin--Tate quotient polynomial

The primitive quotient at level `n + 1` has natural degree
`(q - 1) * q ^ n`. This proves the published M339.016 target for arbitrary
`π` in the valuation ring, with no uniformizer hypothesis.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.016: the primitive quotient polynomial has degree
`(q - 1) * q ^ n`. -/
theorem standardLubinTatePrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomial_natDegreeStatement F π n := by
  unfold standardLubinTatePrimitivePolynomial_natDegreeStatement
  have hdegree :
      (standardLubinTatePolynomial F π).natDegree =
        Nat.card F.residueField := by
    rw [standardLubinTatePolynomial,
      Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow _
    · rw [Polynomial.natDegree_X_pow]
      calc
        (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le π 1
        _ < Nat.card F.residueField :=
          (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hiterate :
      (standardLubinTatePolynomialIterate F π n).natDegree =
        Nat.card F.residueField ^ n := by
    rw [standardLubinTatePolynomialIterate,
      Polynomial.natDegree_iterate_comp, hdegree,
      Polynomial.natDegree_X, mul_one]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [standardLubinTatePrimitivePolynomial,
    Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow, hiterate]
  · rw [Polynomial.natDegree_pow, hiterate, Polynomial.natDegree_C]
    exact hpos

end Langlands.NYLL.LubinTate

end
