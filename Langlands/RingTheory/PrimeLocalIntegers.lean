import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Algebra.Rat

/-! # The localization `ℤ_(p)` of the integers at a prime -/

noncomputable section

namespace Langlands

variable (p : ℕ) [hp : Fact p.Prime]

/-- The ideal `pℤ` is prime. -/
instance primeLocalIntegers_isPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

/-- `ℤ_(p)`: the localization of `ℤ` at the prime ideal `pℤ`, so that exactly the integers
not divisible by `p` become units. -/
abbrev PrimeLocalIntegers : Type :=
  Localization.AtPrime (Ideal.span {(p : ℤ)})

namespace PrimeLocalIntegers

/-- An integer lies in the inverted multiplicative set exactly when `p` does not divide it. -/
theorem mem_primeCompl_iff (m : ℤ) :
    m ∈ (Ideal.span {(p : ℤ)}).primeCompl ↔ ¬ (p : ℤ) ∣ m := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

/-- A natural number prime to `p` is not divisible by `p` as an integer. -/
theorem natCast_mem_primeCompl {n : ℕ} (hn : n.Coprime p) :
    (n : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
  rw [mem_primeCompl_iff, Int.natCast_dvd_natCast]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hn.symm

/-- Every natural number prime to `p` is a unit in `ℤ_(p)`. -/
theorem isUnit_natCast {n : ℕ} (hn : n.Coprime p) : IsUnit (n : PrimeLocalIntegers p) := by
  have h := IsLocalization.map_units (PrimeLocalIntegers p)
    (⟨(n : ℤ), natCast_mem_primeCompl p hn⟩ : (Ideal.span {(p : ℤ)}).primeCompl)
  simpa using h

/-- A natural number prime to the prime `p` is nonzero. -/
theorem ne_zero_of_coprime {n : ℕ} (hn : n.Coprime p) : n ≠ 0 := by
  rintro rfl
  exact hp.out.one_lt.ne' (Nat.coprime_zero_left p |>.mp hn)

variable {p}

/-- In a commutative ring in which every natural number prime to `p` is a unit, every integer
not divisible by `p` is a unit. -/
theorem isUnit_intCast_of_mem {R : Type*} [CommRing R]
    (h : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) (m : (Ideal.span {(p : ℤ)}).primeCompl) :
    IsUnit (Int.castRingHom R m) := by
  obtain ⟨m, hm⟩ := m
  have hcop : m.natAbs.Coprime p := by
    rw [mem_primeCompl_iff, Int.natCast_dvd] at hm
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm).symm
  change IsUnit ((m : ℤ) : R)
  rcases Int.natAbs_eq m with hm' | hm'
  · rw [hm', Int.cast_natCast]
    exact h _ hcop
  · rw [hm', Int.cast_neg, Int.cast_natCast]
    exact (h _ hcop).neg

/-- The unique ring homomorphism from `ℤ_(p)` to a commutative ring in which every natural
number prime to `p` is a unit. -/
def lift {R : Type*} [CommRing R] (h : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) :
    PrimeLocalIntegers p →+* R :=
  IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) (g := Int.castRingHom R)
    (isUnit_intCast_of_mem h)

/-- Any two ring homomorphisms out of `ℤ_(p)` agree. -/
theorem ringHom_ext {R : Type*} [Semiring R] (f g : PrimeLocalIntegers p →+* R) : f = g :=
  IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

/-- The lift is the unique ring homomorphism. -/
theorem lift_unique {R : Type*} [CommRing R] (h : ∀ n : ℕ, n.Coprime p → IsUnit (n : R))
    (f : PrimeLocalIntegers p →+* R) : f = lift h :=
  ringHom_ext f (lift h)

/-- Every natural number prime to `p` is nonzero, hence a unit, in `ℚ`. -/
theorem isUnit_natCast_rat (n : ℕ) (hn : n.Coprime p) : IsUnit (n : ℚ) :=
  isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_zero_of_coprime p hn)

variable (p) in
/-- The inclusion of `ℤ_(p)` into `ℚ`. -/
def toRat : PrimeLocalIntegers p →+* ℚ :=
  lift isUnit_natCast_rat

/-- The inclusion into `ℚ` is injective: `ℤ_(p)` is a subring of `ℚ`. -/
theorem toRat_injective : Function.Injective (toRat p) := by
  have hM : (Ideal.span {(p : ℤ)}).primeCompl ≤ nonZeroDivisors ℤ :=
    Ideal.primeCompl_le_nonZeroDivisors _
  rw [toRat, lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (PrimeLocalIntegers p) hM).eq_iff]
  simp

end PrimeLocalIntegers

end Langlands
