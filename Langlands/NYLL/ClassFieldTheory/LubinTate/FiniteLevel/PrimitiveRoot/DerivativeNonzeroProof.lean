/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 569, 2026-11-16: adapt the M341.009 proof at NYLL
commit fbd320cd8b1b06487c58227e92eb135794267709 to the published
Langlands.NYLL definitions and exact Prop target. Replace the monicity
argument by nonvanishing deduced from the nonzero derivative. Retain the
M341.004 mapping calculation as a private helper. See paired Markdown.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.SeparableRootStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.IterateDerivativeEvalZeroProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.ResidueCardSubOneNonzeroProof
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private theorem primitivePolynomialOverField_formula
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField F π n =
      (standardLubinTatePolynomialIterate F π n).map
          (algebraMap F.valuationSubring K) ^
        (Nat.card F.residueField - 1) +
      Polynomial.C (π : K) := by
  simp [standardLubinTatePrimitivePolynomialOverField,
    standardLubinTatePrimitivePolynomial]

private theorem derivative_ne_zero_of_inputs
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (hiterate : (standardLubinTatePolynomialIterate F π n).derivative.eval 0 = π ^ n)
    (hcard : ((Nat.card F.residueField - 1 : ℕ) : K) ≠ 0) :
    standardLubinTatePrimitivePolynomialOverField_derivative_ne_zeroStatement hπ n := by
  let A :=
    (standardLubinTatePolynomialIterate F π n).map
      (algebraMap F.valuationSubring K)
  have hAderivativeAtZero :
      A.derivative.eval 0 = (π : K) ^ n := by
    calc
      A.derivative.eval 0 =
          algebraMap F.valuationSubring K
            ((standardLubinTatePolynomialIterate F π n).derivative.eval 0) := by
        dsimp [A]
        rw [Polynomial.derivative_map, Polynomial.eval_zero_map,
          Algebra.algebraMap_ofSubsemiring_apply]
      _ = (π : K) ^ n := by
        rw [hiterate, map_pow]
        rfl
  have hAderivative : A.derivative ≠ 0 := by
    intro hzero
    apply pow_ne_zero n hπ.ne_zero
    calc
      (π : K) ^ n = A.derivative.eval 0 := hAderivativeAtZero.symm
      _ = 0 := by rw [hzero, Polynomial.eval_zero]
  have hA : A ≠ 0 := by
    intro hzero
    apply hAderivative
    rw [hzero, Polynomial.derivative_zero]
  change (standardLubinTatePrimitivePolynomialOverField F π n).derivative ≠ 0
  rw [primitivePolynomialOverField_formula]
  change
    (A ^ (Nat.card F.residueField - 1) +
      Polynomial.C (π : K)).derivative ≠ 0
  rw [Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_C, add_zero]
  exact mul_ne_zero
    (mul_ne_zero (Polynomial.C_ne_zero.mpr hcard) (pow_ne_zero _ hA))
    hAderivative

/-- The field-valued primitive polynomial has nonzero derivative. -/
theorem standardLubinTatePrimitivePolynomialOverField_derivative_ne_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField_derivative_ne_zeroStatement hπ n := by
  exact derivative_ne_zero_of_inputs hπ n
    (standardLubinTatePolynomialIterate_derivative_eval_zero F π n)
    (residueFieldNatCard_sub_one_cast_ne_zero F)

end Langlands.NYLL.LubinTate
