/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 776, 2026-11-16: extract the proof of M339.011
(source lines 156–163) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; use the published
Langlands.NYLL target and definitions, inline the degree calculation
from M339.006 (lines 101–114), and use focused imports.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Statements
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree of standard Lubin--Tate polynomial iterates

This module proves the exact published M339.011 target for every element
of the valuation subring and every natural iterate index.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.011: the `n`-fold standard compositional iterate has degree
`q ^ n`, where `q` is the residue-field cardinality. -/
theorem standardLubinTatePolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate_natDegreeStatement F π n := by
  have hdegree : (standardLubinTatePolynomial F π).natDegree =
      Nat.card F.residueField := by
    rw [standardLubinTatePolynomial]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow _
    · rw [Polynomial.natDegree_X_pow]
      calc
        (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le π 1
        _ < Nat.card F.residueField :=
          (Finite.one_lt_card : 1 < Nat.card F.residueField)
  unfold standardLubinTatePolynomialIterate_natDegreeStatement
  rw [standardLubinTatePolynomialIterate,
    Polynomial.natDegree_iterate_comp, hdegree,
    Polynomial.natDegree_X, mul_one]

end Langlands.NYLL.LubinTate

end
