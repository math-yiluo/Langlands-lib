/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 298, 2026-11-13: extract the private M346.029 type from
commit fbd320cd8b1b06487c58227e92eb135794267709 as a public Prop target,
qualify the namespace, reduce imports and omit the proof.
The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Basic

namespace Langlands.NYLL.PortInternal.M346

set_option linter.unusedVariables false in
/-- If every mapped coefficient belongs to an ideal, so does the polynomial's
evaluation at any element of the target semiring. -/
def d029Statement
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) : Prop :=
  P.eval₂ f z ∈ I

end Langlands.NYLL.PortInternal.M346
