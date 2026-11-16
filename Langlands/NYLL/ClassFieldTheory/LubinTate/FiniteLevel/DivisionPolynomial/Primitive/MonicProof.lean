/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 669, 2026-11-16: extract the proof of M339.017 from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify the
namespace with Langlands.NYLL, import the published primitive target,
and state the theorem using that fully applied target. Derive the needed
base and iterate facts locally from the published definitions, adapting
M339.006, M339.007, M339.011 and M339.012. See the paired Markdown for the
complete modification record. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Statements
import Mathlib.Algebra.Polynomial.Monic

/-!
# Monicity of the primitive Lubin--Tate quotient polynomial

This module proves the published M339.017 target for arbitrary elements
of the valuation ring, using local degree and monicity calculations.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.017: the primitive quotient polynomial is monic. -/
theorem standardLubinTatePrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomial_monicStatement F π n := by
  have hq : 1 < Nat.card F.residueField := Finite.one_lt_card
  have hbaseDegree :
      (standardLubinTatePolynomial F π).natDegree =
        Nat.card F.residueField := by
    rw [standardLubinTatePolynomial]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow _
    · rw [Polynomial.natDegree_X_pow]
      calc
        (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le π 1
        _ < Nat.card F.residueField := hq
  have hbaseMonic : (standardLubinTatePolynomial F π).Monic := by
    rw [standardLubinTatePolynomial]
    refine (Polynomial.monic_X_pow _).add_of_left ?_
    calc
      (Polynomial.C π * Polynomial.X).degree ≤ 1 :=
        Polynomial.degree_C_mul_X_le π
      _ < (Polynomial.X ^ Nat.card F.residueField :
          Polynomial F.valuationSubring).degree := by
        rw [Polynomial.degree_X_pow]
        exact_mod_cast hq
  have hiterDegree (m : ℕ) :
      (standardLubinTatePolynomialIterate F π m).natDegree =
        Nat.card F.residueField ^ m := by
    rw [standardLubinTatePolynomialIterate,
      Polynomial.natDegree_iterate_comp, hbaseDegree,
      Polynomial.natDegree_X, mul_one]
  have hiterMonic (m : ℕ) :
      (standardLubinTatePolynomialIterate F π m).Monic := by
    induction m with
    | zero =>
        simp [standardLubinTatePolynomialIterate]
    | succ m ih =>
        rw [standardLubinTatePolynomialIterate, Function.iterate_succ_apply']
        exact hbaseMonic.comp ih (by
          change (standardLubinTatePolynomialIterate F π m).natDegree ≠ 0
          rw [hiterDegree]
          exact pow_ne_zero m (ne_of_gt (Nat.zero_lt_one.trans hq)))
  change (standardLubinTatePolynomialIterate F π n ^
    (Nat.card F.residueField - 1) + Polynomial.C π).Monic
  have hmain :
      (standardLubinTatePolynomialIterate F π n ^
        (Nat.card F.residueField - 1)).Monic :=
    (hiterMonic n).pow _
  refine hmain.add_of_left ?_
  calc
    (Polynomial.C π).degree ≤ 0 := Polynomial.degree_C_le
    _ < (standardLubinTatePolynomialIterate F π n ^
        (Nat.card F.residueField - 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hmain.ne_zero,
        Polynomial.natDegree_pow, hiterDegree]
      exact_mod_cast Nat.mul_pos
        (Nat.sub_pos_of_lt hq) (Nat.pow_pos Nat.card_pos)

end Langlands.NYLL.LubinTate

end
