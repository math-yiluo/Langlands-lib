/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.005 (source lines 196–203) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d005 whose type is the published target
Langlands.NYLL.PortInternal.M351.d005Statement applied to the source binders.
The source proof is kept, after an opening unfold of the target.
The original LICENSE and NOTICE remain in licenses/NYLL/.
Worker 499, 16 November 2026: reuse the shared draft proof and refine its
paired Markdown for this focused proof task.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements

/-!
# Proof of M351.005: the order of a monomial

The monomial `c X^d` has order at least the total degree of `d`. See the paired
Markdown.
-/

universe u v

namespace Langlands.NYLL.PortInternal.M351

/-- M351.005 (source private `degree_le_order_monomial_stabilization`): the
order of the monomial `c X^d` is at least the total degree of `d`. -/
theorem d005
    {R : Type u} [CommRing R] {τ : Type v}
    (d : τ →₀ ℕ) (c : R) :
    d005Statement d c := by
  unfold d005Statement
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

end Langlands.NYLL.PortInternal.M351
