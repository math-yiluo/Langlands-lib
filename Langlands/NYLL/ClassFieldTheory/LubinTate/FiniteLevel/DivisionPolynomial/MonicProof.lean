/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 775, 2026-11-16: extract the proof of M339.007
(lines 116–128) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace with
Langlands.NYLL; use the fully applied published Statement as the theorem
type and unfold it before the original proof; replace the source imports
by the published target module and Mathlib.Algebra.Polynomial.Monic;
replace the module documentation and add the paired Markdown.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.DegreeStatements
import Mathlib.Algebra.Polynomial.Monic

/-!
# Monicity of the standard Lubin--Tate polynomial

This module proves the published M339.007 target for every element of the
valuation ring. The finite residue field has cardinality greater than one,
so adding the linear term to the monic power of `X` preserves monicity.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.007: the standard Lubin--Tate polynomial is monic. -/
theorem standardLubinTatePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    standardLubinTatePolynomial_monicStatement F π := by
  unfold standardLubinTatePolynomial_monicStatement
  rw [standardLubinTatePolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  calc
    (Polynomial.C π * Polynomial.X).degree ≤ 1 :=
      Polynomial.degree_C_mul_X_le π
    _ < (Polynomial.X ^ Nat.card F.residueField :
        Polynomial F.valuationSubring).degree := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

end Langlands.NYLL.LubinTate

end
