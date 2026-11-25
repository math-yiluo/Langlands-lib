/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Inverting `1 - t · shift` on sequences of bounded continuous functions

Let `T` be a complete normed commutative ring all of whose elements have norm at most `1` (for
instance the ring of integers of a nonarchimedean local field), and `t ∈ T` with `‖t‖ < 1`. For
every topological space `W`, the map `(yₙ)ₙ ↦ (yₙ - t y_{n+1})ₙ` on sequences of continuous maps
`W → T` is bijective (`ContinuousMap.bijective_sub_const_mul_succ`): its inverse is
`(xₙ)ₙ ↦ (∑ₖ tᵏ x_{n+k})ₙ`, a uniformly convergent series, and an element of its kernel satisfies
`yₙ = tᵏ y_{n+k}` for all `k`, hence vanishes.
-/

@[expose] public section

namespace ContinuousMap

variable {T : Type*} [NormedCommRing T] [NormOneClass T] [CompleteSpace T] {W : Type*}
  [TopologicalSpace W]

/-- **Inverting `1 - t · shift`.** If all elements of the complete normed ring `T` have norm at
most `1` and `‖t‖ < 1`, then `(yₙ)ₙ ↦ (yₙ - t y_{n+1})ₙ` is a bijection of `ℕ → C(W, T)`. -/
theorem bijective_sub_const_mul_succ (hT : ∀ x : T, ‖x‖ ≤ 1) {t : T} (ht : ‖t‖ < 1) :
    Function.Bijective fun y : ℕ → C(W, T) ↦ fun n ↦ y n - ContinuousMap.const W t * y (n + 1) := by
  have hg : Summable fun k : ℕ ↦ ‖t‖ ^ k := summable_geometric_of_lt_one (norm_nonneg _) ht
  have hb (x : ℕ → C(W, T)) (n k : ℕ) (w : W) : ‖t ^ k * x (n + k) w‖ ≤ ‖t‖ ^ k :=
    (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hT _)).trans
      (norm_pow_le _ _))
  refine ⟨fun y y' h ↦ ?_, fun x ↦ ?_⟩
  · -- the difference `d` of two preimages satisfies `dₙ = t d_{n+1}`, hence `dₙ = tᵏ d_{n+k}`
    have hd (n : ℕ) : y n - y' n = ContinuousMap.const W t * (y (n + 1) - y' (n + 1)) := by
      have := congrFun h n
      dsimp only at this
      linear_combination this
    have hk (k n : ℕ) :
        y n - y' n = ContinuousMap.const W (t ^ k) * (y (n + k) - y' (n + k)) := by
      induction k generalizing n with
      | zero => simp
      | succ k ih =>
        rw [ih, hd (n + k), ← mul_assoc, ← add_assoc]
        congr 1
        ext w
        simp [pow_succ]
    funext n
    refine ContinuousMap.ext fun w ↦ sub_eq_zero.1 (norm_le_zero_iff.1 ?_)
    have h0 : Filter.Tendsto (fun k : ℕ ↦ ‖t‖ ^ k * 2) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg t) ht).mul_const 2
    refine ge_of_tendsto' h0 fun k ↦ ?_
    have hw := congrArg (fun f : C(W, T) ↦ f w) (hk k n)
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply] at hw
    rw [hw]
    refine (norm_mul_le _ _).trans (mul_le_mul (norm_pow_le _ _) ((norm_sub_le _ _).trans ?_)
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    linarith [hT (y (n + k) w), hT (y' (n + k) w)]
  · -- the preimage `yₙ = ∑ₖ tᵏ x_{n+k}`
    have hs (n : ℕ) (w : W) : Summable fun k ↦ t ^ k * x (n + k) w :=
      Summable.of_norm_bounded hg (hb x n · w)
    let y (n : ℕ) : C(W, T) := ⟨fun w ↦ ∑' k, t ^ k * x (n + k) w,
      continuous_tsum (fun k ↦ continuous_const.mul (x (n + k)).continuous) hg (hb x n)⟩
    refine ⟨y, funext fun n ↦ ContinuousMap.ext fun w ↦ ?_⟩
    simp only [y, ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      ContinuousMap.coe_mk]
    rw [(hs n w).tsum_eq_zero_add, ← (hs (n + 1) w).tsum_mul_left]
    simp only [pow_zero, one_mul, add_zero, pow_succ, mul_assoc]
    rw [add_sub_assoc, sub_eq_zero.2, add_zero]
    refine tsum_congr fun k ↦ ?_
    rw [mul_left_comm, add_assoc, add_comm 1 k]

end ContinuousMap
