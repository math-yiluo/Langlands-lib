/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 573, 14 November 2026: adapt source unit M395.001 from
upstream fbd320cd8b1b06487c58227e92eb135794267709 to prove the published
Langlands.NYLL.PortInternal.M395.d001Statement. Import its Library module,
use the planned public internal name, and introduce the complete closed target
with independent universes u and v. The induction proof is retained.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity.Statements

namespace Langlands.NYLL.PortInternal.M395

/-- Pointwise comparison on a multiset implies comparison of product valuations. -/
theorem d001.{u, v} : d001Statement.{u, v} := by
  intro R _ _ _ α s f g h
  induction s using Multiset.induction_on with
  | empty => exact le_rfl
  | @cons z s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons,
        IsDiscreteValuationRing.addVal_mul,
        IsDiscreteValuationRing.addVal_mul]
      apply add_le_add
      · exact h z (Multiset.mem_cons_self z s)
      · apply ih
        intro t ht
        exact h t (by simp [ht])

end Langlands.NYLL.PortInternal.M395
