/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 572, 2026-11-16: extract only the proof of M339.006
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
qualify the namespace with Langlands.NYLL; use the fully applied published
Statement as the theorem type and unfold it before the original proof;
replace source imports by the published target and focused Mathlib degree
operations; replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.DegreeStatements
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Natural degree of the standard Lubin--Tate polynomial

This module proves M339.006 at its published target for every element of the
valuation ring. The term `C π * X` has natural degree at most one, strictly
less than the cardinality of the finite residue field.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.006: the standard Lubin--Tate polynomial has degree `q`. -/
theorem standardLubinTatePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    standardLubinTatePolynomial_natDegreeStatement F π := by
  unfold standardLubinTatePolynomial_natDegreeStatement
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

end Langlands.NYLL.LubinTate

end
