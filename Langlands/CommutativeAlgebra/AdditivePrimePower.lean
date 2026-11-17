import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Additive power maps and the characteristic -/

noncomputable section

universe u

open Polynomial

namespace Langlands.CommutativeAlgebra

/-- If the binomial coefficients `C(pⁿ, k)` with `0 < k < pⁿ` vanish in a ring, then so
does the prime `p`. -/
theorem natCast_prime_eq_zero_of_choose {A : Type*} [CommRing A] {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (h : ∀ k, 0 < k → k < p ^ n → ((p ^ n).choose k : A) = 0) :
    (p : A) = 0 := by
  have hp1 : 1 < p := hp.one_lt
  have hlt : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp1 (by omega)
  set N := (p ^ n).choose (p ^ (n - 1)) with hN
  have hN0 : N ≠ 0 := (Nat.choose_pos hlt.le).ne'
  have hfac : N.factorization p = 1 := by
    rw [hN, Nat.factorization_choose_prime_pow hp hlt.le (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]
    omega
  set m := N / p ^ N.factorization p with hm
  have hNm : p * m = N := by
    have := Nat.ordProj_mul_ordCompl_eq_self N p
    rw [hfac, pow_one] at this
    rw [hm, hfac, pow_one]
    exact this
  have hpm : ¬ p ∣ m := by
    have := Nat.not_dvd_ordCompl hp hN0
    rwa [← hm] at this
  have hcop : Nat.Coprime m (p ^ (n - 1)) :=
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : ((p * m : ℕ) : A) = 0 := by
    rw [hNm]
    exact h _ (pow_pos hp.pos _) hlt
  have h2 : ((p ^ n : ℕ) : A) = 0 := by
    have := h 1 one_pos (Nat.one_lt_pow hn hp1)
    rwa [Nat.choose_one_right] at this
  have key : (p : A) = (a : A) * ((p * m : ℕ) : A) + (b : A) * ((p ^ n : ℕ) : A) := by
    have e : ((a * (m : ℤ) + b * ((p ^ (n - 1) : ℕ) : ℤ) : ℤ) : A) = 1 := by
      rw [hab, Int.cast_one]
    have hpn : p ^ n = p * p ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc (p : A) = (p : A) * ((a * (m : ℤ) + b * ((p ^ (n - 1) : ℕ) : ℤ) : ℤ) : A) := by
          rw [e, mul_one]
      _ = (a : A) * ((p * m : ℕ) : A) + (b : A) * ((p ^ n : ℕ) : A) := by
          rw [hpn]
          push_cast
          ring
  rw [key, h1, h2, mul_zero, mul_zero, add_zero]

/-- If the scaled power `c x ^ q` is additive on the two variables of `B₀[X][X]`, that is
`c (X + Y) ^ q = c X ^ q + c Y ^ q` with `Y` the inner variable, then `c` kills the binomial
coefficients `C(q, k)` with `0 < k < q`. -/
theorem mul_choose_eq_zero_of_add_pow {B₀ : Type*} [CommRing B₀] (c : B₀) (q : ℕ)
    (h : algebraMap B₀ B₀[X][X] c * (X + Polynomial.C X) ^ q =
      algebraMap B₀ B₀[X][X] c * X ^ q + algebraMap B₀ B₀[X][X] c * (Polynomial.C X) ^ q)
    (k : ℕ) (hk0 : 0 < k) (hkq : k < q) : c * (q.choose k : B₀) = 0 := by
  simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have hc := congrArg (fun g : B₀[X][X] => (g.coeff k).coeff (q - k)) h
  simp only [coeff_add, coeff_C_mul, coeff_X_add_C_pow, coeff_X_pow, ← C_pow, ← C_mul,
    coeff_C, ite_eq_right hkq.ne, ite_eq_right hk0.ne', mul_zero, add_zero, coeff_zero] at hc
  rw [← C_eq_natCast, mul_comm (X ^ (q - k)), coeff_C_mul_X_pow, ite_eq_left rfl] at hc
  exact hc

/-- If `c` is a unit and the scaled prime-power map `x ↦ c x ^ (p ^ n)`, `n ≠ 0`, is additive
on the two variables of `B₀[X][X]`, then the prime `p` vanishes in `B₀`. -/
theorem natCast_prime_eq_zero_of_add_pow {B₀ : Type*} [CommRing B₀] {c : B₀} {p n : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) (hc : IsUnit c)
    (h : algebraMap B₀ B₀[X][X] c * (X + Polynomial.C X) ^ (p ^ n) =
      algebraMap B₀ B₀[X][X] c * X ^ (p ^ n) +
        algebraMap B₀ B₀[X][X] c * (Polynomial.C X) ^ (p ^ n)) :
    (p : B₀) = 0 :=
  natCast_prime_eq_zero_of_choose hp hn fun k hk0 hkq =>
    (hc.mul_right_eq_zero).1 (mul_choose_eq_zero_of_add_pow c _ h k hk0 hkq)

end Langlands.CommutativeAlgebra
