import Langlands.GroupScheme.Dynamic.GeneralLinearWeightComponents
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Roots

/-! # Lowest-weight limits of homogeneous polynomial equations -/

namespace Langlands.GroupScheme.FlagCore

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ]

/-- The weight-`c` part of a vector `v` for integer coordinate weights `d`: the coordinates
of weight `c` are kept and all others are replaced by zero. -/
def weightPart (d : σ → ℤ) (v : σ → k) (c : ℤ) : σ → k :=
  GeneralLinear.weightPart d c v

/-- Evaluating a homogeneous polynomial of degree `m` at a scaled vector multiplies the
value by the `m`-th power of the scalar. -/
theorem eval_smul_of_isHomogeneous {f : MvPolynomial σ k} {m : ℕ} (hf : f.IsHomogeneous m)
    (a : k) (x : σ → k) : eval (a • x) f = a ^ m * eval x f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hd)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The limit lemma for a cocharacter acting diagonally with integer weights `d`.
If a homogeneous polynomial vanishes on every translate `(z ^ d i * v i)_i` with `z ≠ 0`
over an infinite field, and `c` is at most every weight occurring in `v`, then it vanishes
on the weight-`c` part of `v`. -/
theorem eval_weightPart_eq_zero [Infinite k] {f : MvPolynomial σ k} {m : ℕ}
    (hf : f.IsHomogeneous m) (d : σ → ℤ) (v : σ → k) (c : ℤ)
    (hc : ∀ i, v i ≠ 0 → c ≤ d i)
    (h : ∀ z : k, z ≠ 0 → eval (fun i => z ^ d i * v i) f = 0) :
    eval (weightPart d v c) f = 0 := by
  classical
  set e : σ → ℕ := fun i => (d i - c).toNat with he
  set P : Polynomial k :=
    aeval (fun i => Polynomial.C (v i) * Polynomial.X ^ e i) f with hP
  have hPeval : ∀ z : k, P.eval z = eval (fun i => v i * z ^ e i) f := by
    intro z
    rw [hP, ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval,
      ← MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    simp
  have hroot : ∀ z : k, z ≠ 0 → P.IsRoot z := by
    intro z hz
    have hvec : (fun i => z ^ d i * v i) = z ^ c • fun i => v i * z ^ e i := by
      funext i
      by_cases hv : v i = 0
      · simp [hv]
      · have hci := hc i hv
        have hd : d i = c + (e i : ℤ) := by
          simp only [he]
          rw [Int.toNat_of_nonneg (by omega)]
          ring
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hd, zpow_add₀ hz, zpow_natCast]
        ring
    have h0 := h z hz
    rw [hvec, eval_smul_of_isHomogeneous hf] at h0
    rw [Polynomial.IsRoot.def, hPeval]
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (zpow_ne_zero _ hz))
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({0} : Set k)ᶜ)
    · intro z hz
      exact hroot z hz
    · exact (Set.finite_singleton 0).infinite_compl
  have h0 := hPeval 0
  rw [hPzero, Polynomial.eval_zero] at h0
  have hvec : weightPart d v c = fun i => v i * (0 : k) ^ e i := by
    funext i
    simp only [weightPart, GeneralLinear.weightPart]
    by_cases hv : v i = 0
    · simp [hv]
    · have hci := hc i hv
      by_cases hdi : d i = c
      · simp [hdi, he]
      · have hpos : e i ≠ 0 := by
          simp only [he]
          omega
        simp [hdi, zero_pow hpos]
  rw [hvec]
  exact h0.symm

end Langlands.GroupScheme.FlagCore
