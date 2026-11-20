import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Order.Lattice

/-! # A uniform lower bound among the first power sums -/

noncomputable section

set_option autoImplicit false

open Finset

namespace Langlands.Analysis

/-- The first `n` power sums of an `n`-tuple of sup norm at least one
cannot all have arbitrarily small norm for fixed `n > 0`. -/
def UniformPowerSumLowerBoundStatement : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin n → ℂ, 1 ≤ ‖z‖ →
    ∃ k ∈ Icc 1 n, ε ≤ ‖∑ i, z i ^ k‖

private theorem eq_zero_of_powerSums_eq_zero {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k ∈ Icc 1 n, ∑ i, z i ^ k = 0) : z = 0 := by
  classical
  have he (k : ℕ) (hk : k ∈ Icc 1 n) :
      MvPolynomial.eval z (MvPolynomial.esymm (Fin n) ℂ k) = 0 := by
    have h := congrArg (MvPolynomial.eval z) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)
    simp only [map_natCast, map_mul, map_pow, map_neg, map_one, map_sum] at h
    have hs : (∑ a ∈ antidiagonal k with a.1 < k,
        (-1 : ℂ) ^ a.1 * MvPolynomial.eval z (MvPolynomial.esymm (Fin n) ℂ a.1) *
          MvPolynomial.eval z (MvPolynomial.psum (Fin n) ℂ a.2)) = 0 := by
      apply sum_eq_zero
      intro a ha
      rw [mem_filter, mem_antidiagonal] at ha
      have hk' := mem_Icc.mp hk
      simp [MvPolynomial.psum, hz a.2 (mem_Icc.mpr ⟨by omega, by omega⟩)]
    rw [hs, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (by
      have := (mem_Icc.mp hk).1
      omega))
  funext i
  have hV := congrArg (MvPolynomial.eval z)
    (congrArg (Polynomial.eval (-MvPolynomial.X i : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n)))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin,
    map_prod, map_sum, map_add, map_mul, map_pow, map_neg, MvPolynomial.eval_X] at hV
  have hp : (∏ j : Fin n, (-z i + z j)) = 0 :=
    prod_eq_zero (mem_univ i) (neg_add_cancel (z i))
  have hs : (∑ j ∈ range n, MvPolynomial.eval z (MvPolynomial.esymm (Fin n) ℂ (j + 1)) *
      (-z i) ^ (n - (j + 1))) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [mem_range] at hj
    rw [he _ (mem_Icc.mpr ⟨by omega, by omega⟩), zero_mul]
  rw [hp, sum_range_succ', hs, MvPolynomial.esymm_zero, map_one, one_mul, Nat.sub_zero] at hV
  have hpow : (-z i) ^ n = 0 := by simpa using hV.symm
  change z i = 0
  by_contra hi
  exact pow_ne_zero n (neg_ne_zero.mpr hi) hpow

/-- The maximum of the first `n` power-sum norms has a positive minimum
on the unit sphere. Scaling up preserves the lower bound. -/
theorem uniformPowerSumLowerBound : UniformPowerSumLowerBoundStatement := by
  intro n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let K := Icc 1 n
  have hK : K.Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  let f (k : ℕ) (z : Fin n → ℂ) : ℝ := ‖∑ i, z i ^ k‖
  let M (z : Fin n → ℂ) : ℝ := K.sup' hK (fun k => f k z)
  have hM : Continuous M := Continuous.finset_sup'_apply hK fun k _ =>
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow k).norm
  let S := Metric.sphere (0 : Fin n → ℂ) 1
  have hS : S.Nonempty := ⟨fun _ => 1, by simp [S]⟩
  obtain ⟨a, ha, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS hM.continuousOn
  have hpos : 0 < M a := by
    by_contra! h
    have ha0 : a = 0 := eq_zero_of_powerSums_eq_zero a fun k hk =>
      norm_le_zero_iff.mp ((le_sup' (fun j => f j a) hk).trans h)
    simp [ha0] at ha
  refine ⟨M a, hpos, fun z hz => ?_⟩
  let c : ℂ := (‖z‖ : ℂ)⁻¹
  let w : Fin n → ℂ := c • z
  have hc : ‖c‖ = ‖z‖⁻¹ := by simp [c]
  have hw : w ∈ S := by
    have hzpos : 0 < ‖z‖ := zero_lt_one.trans_le hz
    simp only [S, Metric.mem_sphere, dist_zero_right, w, norm_smul, hc, inv_mul_cancel₀ hzpos.ne']
  have hle : M a ≤ M w := hmin hw
  obtain ⟨k, hk, hkw⟩ := (le_sup'_iff hK).mp hle
  refine ⟨k, hk, hkw.trans ?_⟩
  have hf : f k w = ‖c‖ ^ k * f k z := by
    simp only [f, w, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_sum, norm_mul, norm_pow]
  rw [hf]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg c) (hc ▸ inv_le_one_of_one_le₀ hz))

end Langlands.Analysis
