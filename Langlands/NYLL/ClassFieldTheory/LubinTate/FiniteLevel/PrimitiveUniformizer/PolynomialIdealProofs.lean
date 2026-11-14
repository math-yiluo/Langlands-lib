/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 669, 2026-11-14: port the proof of the private M346.029
helper from commit fbd320cd8b1b06487c58227e92eb135794267709 to the
fully applied published target, qualify its namespace and reduce imports.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer.PolynomialIdealStatements
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace Langlands.NYLL.PortInternal.M346

universe u v

/-- Polynomial evaluation belongs to an ideal containing every mapped coefficient. -/
theorem d029
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) :
    d029Statement f I P z hcoeff := by
  change P.eval₂ f z ∈ I
  rw [Polynomial.eval₂_eq_sum_range]
  exact I.sum_mem fun i _ =>
    Ideal.mul_mem_right (z ^ i) I (hcoeff i)

end Langlands.NYLL.PortInternal.M346
