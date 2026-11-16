/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.008 (source lines 233–257) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d008 whose type is the published target
Langlands.NYLL.PortInternal.M351.d008Statement applied to the source binders.
The source proof (Finset induction with le_order_mul) is kept, after an opening
unfold of the target; its call of the private M351.006 theorem is replaced by a
local copy hpow of that theorem's source proof, so that the module depends only
on the target module and Mathlib.
The original LICENSE and NOTICE remain in licenses/NYLL/.
Worker 187 adopted and checked this proof for Task 6731, 16 November 2026.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements

/-!
# Proof of M351.008: the order of a finite product of powers

If every factor has order at least one, then `∏ i ∈ s, f i ^ n i` has order at
least `∑ i ∈ s, n i`. See the paired Markdown.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

/-- M351.008 (source private
`natCast_sum_le_order_finset_prod_pow_stabilization`): if every factor has
order at least one, then `∏ i ∈ s, f i ^ n i` has order at least
`∑ i ∈ s, n i`. -/
theorem d008
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    d008Statement f n hf := by
  unfold d008Statement
  have hpow (h : MvPowerSeries τ R) (k : ℕ) (hh : (1 : ℕ∞) ≤ h.order) :
      (k : ℕ∞) ≤ (h ^ k).order :=
    calc
      (k : ℕ∞) = k • (1 : ℕ∞) := by rw [nsmul_eq_mul, mul_one]
      _ ≤ k • h.order := nsmul_le_nsmul_right hh k
      _ ≤ (h ^ k).order := MvPowerSeries.le_order_pow k
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Nat.cast_zero]
      exact bot_le
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (hpow (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

end Langlands.NYLL.PortInternal.M351
