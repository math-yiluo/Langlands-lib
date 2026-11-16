/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 334, 2026-11-16: extract and adapt M341.002
(lines 54–69) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace,
state the theorem using the published Prop target, use its focused
import, and prove the required zero evaluations locally by joint
induction. The original simp attribute is retained. See the paired
Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.DerivativeCardinalityStatements

/-!
# Derivative at zero of the standard polynomial iterate

The derivative at zero of the `n`-fold standard Lubin--Tate polynomial
iterate is `π ^ n`, for any element `π` of the valuation subring.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The derivative at zero of the `n`-fold standard iterate is `π ^ n`. -/
@[simp]
theorem standardLubinTatePolynomialIterate_derivative_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate_derivative_eval_zeroStatement F π n := by
  have hq : 1 < Nat.card F.residueField := Finite.one_lt_card
  have hzero : (standardLubinTatePolynomial F π).eval 0 = 0 := by
    simp [standardLubinTatePolynomial, Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)]
  have hderiv : (standardLubinTatePolynomial F π).derivative.eval 0 = π := by
    simp [standardLubinTatePolynomial, Polynomial.derivative_pow,
      Nat.sub_ne_zero_of_lt hq]
  have hsucc (m : ℕ) :
      standardLubinTatePolynomialIterate F π (m + 1) =
        (standardLubinTatePolynomial F π).comp
          (standardLubinTatePolynomialIterate F π m) := by
    simp only [standardLubinTatePolynomialIterate, Function.iterate_succ_apply']
  have hboth (m : ℕ) :
      (standardLubinTatePolynomialIterate F π m).eval 0 = 0 ∧
        (standardLubinTatePolynomialIterate F π m).derivative.eval 0 = π ^ m := by
    induction m with
    | zero =>
        simp [standardLubinTatePolynomialIterate]
    | succ m ih =>
        constructor
        · rw [hsucc, Polynomial.eval_comp, ih.1, hzero]
        · rw [hsucc, Polynomial.derivative_comp, Polynomial.eval_mul, ih.2,
            Polynomial.eval_comp, ih.1, hderiv, pow_succ]
  exact (hboth n).2

end Langlands.NYLL.LubinTate
