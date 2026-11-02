import Langlands.Global.Arithmetic.AlmostEverywherePowerHalfStatement
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Norm.Basic

/-! # Algebraic descent and prime-power assembly for local powers -/

universe u v

namespace Langlands.Global.Arithmetic.PowerDescent

section Fields

variable {K : Type u} [Field K]

/-- A root of a nonzero field element can be recorded as a unit. -/
theorem exists_unit_pow_eq_iff (n : ℕ) (a : Kˣ) :
    (∃ b : Kˣ, b ^ n = a) ↔ ∃ b : K, b ^ n = (a : K) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Units.val hb⟩
  · rintro ⟨b, hb⟩
    by_cases hn : n = 0
    · refine ⟨1, ?_⟩
      apply Units.ext
      simpa [hn] using hb
    · have hb0 : b ≠ 0 := by
        intro h
        exact a.ne_zero (by simpa [h, zero_pow hn] using hb.symm)
      exact ⟨Units.mk0 b hb0, Units.ext hb⟩

/-- Having roots of two coprime orders gives a root of their product. -/
theorem exists_pow_mul_eq_of_coprime {m n : ℕ} (hmn : m.Coprime n) {a : K}
    (hm : ∃ b : K, b ^ m = a) (hn : ∃ c : K, c ^ n = a) :
    ∃ d : K, d ^ (m * n) = a := by
  obtain ⟨b, hb⟩ := hm
  obtain ⟨c, hc⟩ := hn
  obtain ⟨d, hbd, -⟩ := (pow_eq_pow_iff_of_coprime hmn).1 (hb.trans hc.symm)
  exact ⟨d, by rw [Nat.mul_comm m n, pow_mul, ← hbd, hb]⟩

/-- The unit-valued version of coprime-power assembly. -/
theorem exists_unit_pow_mul_eq_of_coprime {m n : ℕ} (hmn : m.Coprime n) {a : Kˣ}
    (hm : ∃ b : Kˣ, b ^ m = a) (hn : ∃ c : Kˣ, c ^ n = a) :
    ∃ d : Kˣ, d ^ (m * n) = a :=
  (exists_unit_pow_eq_iff _ _).2
    (exists_pow_mul_eq_of_coprime hmn
      ((exists_unit_pow_eq_iff _ _).1 hm) ((exists_unit_pow_eq_iff _ _).1 hn))

/-- Roots of each prime-power divisor assemble to a root of a positive order. -/
theorem exists_unit_pow_eq_of_prime_power_dvd {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (hprime : ∀ p r : ℕ, p.Prime → 0 < r → p ^ r ∣ n →
      ∃ b : Kˣ, b ^ (p ^ r) = a) :
    ∃ b : Kˣ, b ^ n = a := by
  have h : ∀ m : ℕ, m ∣ n → ∃ b : Kˣ, b ^ m = a := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p r hp hr hdiv
      exact hprime p r hp hr hdiv
    · intro hdiv
      exact (hn (zero_dvd_iff.1 hdiv)).elim
    · intro _
      exact ⟨a, pow_one a⟩
    · intro m k _ _ hmk hm hk hdiv
      exact exists_unit_pow_mul_eq_of_coprime hmk
        (hm ((dvd_mul_right m k).trans hdiv))
        (hk ((dvd_mul_left k m).trans hdiv))
  exact h n (dvd_refl n)

variable {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Taking norms of a root in a finite extension gives a root of the degree power. -/
theorem exists_pow_eq_degree_of_root {n : ℕ} {a : K}
    (hroot : ∃ b : L, b ^ n = algebraMap K L a) :
    ∃ c : K, c ^ n = a ^ Module.finrank K L := by
  obtain ⟨b, hb⟩ := hroot
  refine ⟨Algebra.norm K b, ?_⟩
  rw [← map_pow, hb, Algebra.norm_algebraMap]

/-- An order coprime to the extension degree descends by the norm and Bézout. -/
theorem exists_pow_eq_of_coprime_degree {n : ℕ}
    (hcop : (Module.finrank K L).Coprime n) {a : K}
    (hroot : ∃ b : L, b ^ n = algebraMap K L a) :
    ∃ c : K, c ^ n = a := by
  exact (pow_mem_range_pow_of_coprime hcop a).1
    (exists_pow_eq_degree_of_root hroot)

/-- Coprime-degree norm descent in multiplicative groups. -/
theorem exists_unit_pow_eq_of_coprime_degree {n : ℕ}
    (hcop : (Module.finrank K L).Coprime n) {a : Kˣ}
    (hroot : ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    ∃ c : Kˣ, c ^ n = a := by
  apply (exists_unit_pow_eq_iff _ _).2
  apply exists_pow_eq_of_coprime_degree hcop
  obtain ⟨b, hb⟩ := hroot
  exact ⟨b, congrArg Units.val hb⟩

end Fields

section LocalPowers

variable {K : Type u} [Field K] [NumberField K]

/-- Local powers remain powers of any divisor of the original order. -/
theorem local_power_of_dvd {m n : ℕ} (hmn : m ∣ n) {a : Kˣ}
    (v : FinitePlace K)
    (h : ∃ b : (FiniteCompletion K v)ˣ,
      b ^ n = Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a) :
    ∃ b : (FiniteCompletion K v)ˣ,
      b ^ m = Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a := by
  obtain ⟨k, rfl⟩ := hmn
  obtain ⟨b, hb⟩ := h
  exact ⟨b ^ k, by rw [← pow_mul, Nat.mul_comm k m, hb]⟩

/-- The general half-power target reduces to its positive prime-power instances. -/
theorem almostEverywherePowerHalf_of_prime_powers
    (hprime : ∀ (K : Type u) [Field K] [NumberField K]
      (S : Finset (FinitePlace K)) (p r : ℕ), p.Prime → 0 < r → ∀ a : Kˣ,
      (∀ v : FinitePlace K, v ∉ S →
        ∃ b : (FiniteCompletion K v)ˣ,
          b ^ (2 * p ^ r) =
            Units.map (algebraMap K (FiniteCompletion K v)).toMonoidHom a) →
      ∃ b : Kˣ, b ^ (p ^ r) = a) :
    AlmostEverywherePowerHalfStatement.{u} := by
  intro K _ _ S n hn a ha
  apply exists_unit_pow_eq_of_prime_power_dvd (Nat.ne_of_gt hn)
  intro p r hp hr hdiv
  apply hprime K S p r hp hr a
  intro v hv
  exact local_power_of_dvd (Nat.mul_dvd_mul_left 2 hdiv) v (ha v hv)

end LocalPowers

end Langlands.Global.Arithmetic.PowerDescent
