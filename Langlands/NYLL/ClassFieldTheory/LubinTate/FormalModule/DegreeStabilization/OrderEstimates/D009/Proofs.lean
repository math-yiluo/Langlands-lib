/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 489, 14 November 2026: proof of the source-private theorem
M351.009 (source lines 259–295) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as the public theorem
Langlands.NYLL.PortInternal.M351.d009 whose type is the published target
Langlands.NYLL.PortInternal.M351.d009Statement applied to the source binders.
The source proof (the factorization f ^ n - g ^ n = (f - g) * q with the
geometric sum q, and a lower bound for the order of q) is kept, after an
opening unfold of the target. Its calls of the private M351.006 theorem are
replaced by a local copy hpow of that theorem's source proof, and its use of
the private M351.007 theorem is replaced by a local lemma hsum proved from
MvPowerSeries.le_order and MvPowerSeries.coeff_of_lt_order, so that the module
depends only on the target module and Mathlib (Mathlib.Algebra.Ring.GeomSum
supplies Commute.mul_geom_sum₂).
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.OrderEstimates.Statements
import Mathlib.Algebra.Ring.GeomSum

/-!
# Proof of M351.009: the order of a difference of two powers

For `f` and `g` of order at least one, `f ^ n - g ^ n` has order at least
`(f - g).order + (n - 1)`. See the paired Markdown.
-/

universe u v

namespace Langlands.NYLL.PortInternal.M351

/-- M351.009 (source private
`order_sub_add_pred_le_order_pow_sub_pow_stabilization`): for `f` and `g` of
order at least one, `f ^ n - g ^ n` has order at least
`(f - g).order + (n - 1)`. -/
theorem d009
    {R : Type u} [CommRing R] {τ : Type v}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    d009Statement f g hf hg n := by
  unfold d009Statement
  have hpow (h : MvPowerSeries τ R) (k : ℕ) (hh : (1 : ℕ∞) ≤ h.order) :
      (k : ℕ∞) ≤ (h ^ k).order :=
    calc
      (k : ℕ∞) = k • (1 : ℕ∞) := by rw [nsmul_eq_mul, mul_one]
      _ ≤ k • h.order := nsmul_le_nsmul_right hh k
      _ ≤ (h ^ k).order := MvPowerSeries.le_order_pow k
  have hsum {t : Finset ℕ} {F : ℕ → MvPowerSeries τ R} {m : ℕ∞}
      (h : ∀ i ∈ t, m ≤ (F i).order) :
      m ≤ (∑ i ∈ t, F i).order := by
    refine MvPowerSeries.le_order fun d hd => ?_
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi =>
      MvPowerSeries.coeff_of_lt_order (hd.trans_le (h i hi))
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply hsum
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (hpow f i hf)
          (hpow g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  have hfactor :
      (f - g) * q = f ^ n - g ^ n := by
    exact (Commute.all f g).mul_geom_sum₂ n
  calc
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
        (f - g).order + q.order :=
      add_le_add_right hq _
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) hfactor

end Langlands.NYLL.PortInternal.M351
