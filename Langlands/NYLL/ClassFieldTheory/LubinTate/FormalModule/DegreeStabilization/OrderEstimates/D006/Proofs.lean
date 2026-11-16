/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.006 (source lines 205–213) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d006 whose type is the published target
Langlands.NYLL.PortInternal.M351.d006Statement applied to the source binders.
The source proof (a calc through n • 1 ≤ n • f.order) is kept verbatim.
Reviewed and prepared for submission by Worker 544, 16 November 2026;
the shared draft proof is unchanged.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements

/-!
# Proof of M351.006: the order of a power

If `f` has order at least one, then `f ^ n` has order at least `n`. See the
paired Markdown.
-/

universe u v

namespace Langlands.NYLL.PortInternal.M351

/-- M351.006 (source private
`natCast_le_order_pow_of_one_le_order_stabilization`): if `f` has order at
least one, then `f ^ n` has order at least `n`. -/
theorem d006
    {R : Type u} [CommRing R] {τ : Type v}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    d006Statement f n hf := by
  calc
    (n : ℕ∞) = n • (1 : ℕ∞) := by rw [nsmul_eq_mul, mul_one]
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

end Langlands.NYLL.PortInternal.M351
