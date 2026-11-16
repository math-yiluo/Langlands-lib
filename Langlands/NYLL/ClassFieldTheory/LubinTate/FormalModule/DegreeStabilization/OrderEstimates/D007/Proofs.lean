/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.007 (source lines 215–231) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d007 whose type is the published target
Langlands.NYLL.PortInternal.M351.d007Statement applied to the source binders.
The source proof (Finset induction with min_order_le_add) is kept, after an
opening unfold of the target.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements

/-!
# Proof of M351.007: the order of a finite sum

A common lower bound for the orders of the summands bounds the order of a
finite sum. See the paired Markdown.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

/-- M351.007 (source private `le_order_finset_sum_stabilization`): a common
lower bound for the orders of the summands bounds the order of a finite sum. -/
theorem d007
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    d007Statement h := by
  unfold d007Statement
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, MvPowerSeries.order_zero]
      exact le_top
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

end Langlands.NYLL.PortInternal.M351
