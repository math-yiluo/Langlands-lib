/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.010 (source lines 297–398) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d010 whose type is the published target
Langlands.NYLL.PortInternal.M351.d010Statement applied to the source binders.
The source proof (Finset induction, splitting the difference of products with
`ring` and bounding both terms with le_order_mul) is kept, after an opening
unfold of the target. Its calls of
the private M351.006, M351.008 and M351.009 theorems are replaced by local
lemmas hpow (the source proof of M351.006), hprod (proved from
MvPowerSeries.le_order_prod) and hpowSub (the source proof of M351.009, with
the finite-sum bound proved from MvPowerSeries.le_order and
MvPowerSeries.coeff_of_lt_order), so that the module depends only on the
target module and Mathlib (Mathlib.Algebra.Ring.GeomSum supplies
Commute.mul_geom_sum₂; Mathlib.Tactic.Ring supplies ring).
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Proof of M351.010: the order of a difference of two products of powers

Under the source hypotheses on `s`, the difference
`∏ i ∈ s, f i ^ n i - ∏ i ∈ s, g i ^ n i` has order at least
`∑ i ∈ s, n i + 1`. See the paired Markdown.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

/-- M351.010 (source private
`natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization`): if every
exponent on `s` is nonzero, all `f i` and `g i` have order at least one and
every `f i - g i` has order at least two, then the difference of the two
finite products of powers has order at least `∑ i ∈ s, n i + 1`. -/
theorem d010
    {R : Type u} [CommRing R] {τ : Type v} {ι : Type w}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    d010Statement f g n hn hf hg hfg := by
  unfold d010Statement
  -- Local copy of M351.006.
  have hpow (h : MvPowerSeries τ R) (k : ℕ) (hh : (1 : ℕ∞) ≤ h.order) :
      (k : ℕ∞) ≤ (h ^ k).order :=
    calc
      (k : ℕ∞) = k • (1 : ℕ∞) := by rw [nsmul_eq_mul, mul_one]
      _ ≤ k • h.order := nsmul_le_nsmul_right hh k
      _ ≤ (h ^ k).order := MvPowerSeries.le_order_pow k
  -- M351.008 for the family `f`, `n` and an arbitrary finite set `t`.
  have hprod (t : Finset ι) (ht : ∀ j ∈ t, (1 : ℕ∞) ≤ (f j).order) :
      ((∑ j ∈ t, n j : ℕ) : ℕ∞) ≤ (∏ j ∈ t, (f j) ^ n j).order :=
    calc
      ((∑ j ∈ t, n j : ℕ) : ℕ∞) = ∑ j ∈ t, (n j : ℕ∞) := Nat.cast_sum t n
      _ ≤ ∑ j ∈ t, ((f j) ^ n j).order :=
        Finset.sum_le_sum fun j hj => hpow (f j) (n j) (ht j hj)
      _ ≤ (∏ j ∈ t, (f j) ^ n j).order :=
        MvPowerSeries.le_order_prod (fun j => (f j) ^ n j) t
  -- Local copy of M351.009, with the bound for the geometric sum proved
  -- coefficientwise.
  have hpowSub (a b : MvPowerSeries τ R)
      (ha : (1 : ℕ∞) ≤ a.order) (hb : (1 : ℕ∞) ≤ b.order) (k : ℕ) :
      (a - b).order + ((k - 1 : ℕ) : ℕ∞) ≤ (a ^ k - b ^ k).order := by
    let q :=
      ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)
    have hq : ((k - 1 : ℕ) : ℕ∞) ≤ q.order := by
      refine MvPowerSeries.le_order fun d hd => ?_
      rw [map_sum]
      refine Finset.sum_eq_zero fun i hi =>
        MvPowerSeries.coeff_of_lt_order (hd.trans_le ?_)
      have hi' : i < k := Finset.mem_range.mp hi
      calc
        ((k - 1 : ℕ) : ℕ∞) =
            (i : ℕ∞) + ((k - 1 - i : ℕ) : ℕ∞) := by
          norm_cast
          omega
        _ ≤ (a ^ i).order + (b ^ (k - 1 - i)).order :=
          add_le_add (hpow a i ha) (hpow b (k - 1 - i) hb)
        _ ≤ (a ^ i * b ^ (k - 1 - i)).order :=
          MvPowerSeries.le_order_mul
    have hfactor :
        (a - b) * q = a ^ k - b ^ k :=
      (Commute.all a b).mul_geom_sum₂ k
    calc
      (a - b).order + ((k - 1 : ℕ) : ℕ∞) ≤
          (a - b).order + q.order :=
        add_le_add_right hq _
      _ ≤ ((a - b) * q).order :=
        MvPowerSeries.le_order_mul
      _ = (a ^ k - b ^ k).order :=
        congrArg (fun h : MvPowerSeries τ R => h.order) hfactor
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, sub_self, MvPowerSeries.order_zero]
      exact le_top
  | @insert i s hi ih =>
      have hni : n i ≠ 0 :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add_left
              (hfg i (Finset.mem_insert_self i s)) _
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            hpowSub
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodF :
          ((∑ j ∈ s, n j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (f j) ^ n j).order :=
        hprod s
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hpowG :
          (n i : ℕ∞) ≤ ((g i) ^ n i).order :=
        hpow
          (g i) (n i) (hg i (Finset.mem_insert_self i s))
      have hprodDifference :
          (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((∏ j ∈ s, (f j) ^ n j) -
              ∏ j ∈ s, (g j) ^ n j).order :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference hprodF
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add hpowG hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

end Langlands.NYLL.PortInternal.M351
