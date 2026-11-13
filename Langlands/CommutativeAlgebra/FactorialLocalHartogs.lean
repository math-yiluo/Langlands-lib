import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Hartogs extension in factorial local rings of dimension at least two -/

namespace Langlands.CommutativeAlgebra.FactorialLocalHartogs

variable {O : Type*} [CommRing O] [IsDomain O] [UniqueFactorizationMonoid O] [IsLocalRing O]

/-- If a nonzero prime lies strictly below the maximal ideal, then no prime element divides
every element of the maximal ideal. -/
theorem exists_mem_maximalIdeal_not_dvd {q : Ideal O} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (hqm : q ≠ IsLocalRing.maximalIdeal O) {p : O} (hp : Prime p) :
    ∃ f ∈ IsLocalRing.maximalIdeal O, ¬ p ∣ f := by
  by_contra h
  push Not at h
  obtain ⟨r, hrq, hr⟩ := hq.exists_mem_prime_of_ne_bot hq0
  have hrm : r ∈ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hq.ne_top hrq
  have hpr : Associated p r := hp.associated_of_dvd hr (h r hrm)
  obtain ⟨u, hu⟩ := hpr.symm
  have hpq : p ∈ q := by
    rw [← hu]
    exact q.mul_mem_right _ hrq
  apply hqm
  apply le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top)
  intro f hf
  obtain ⟨c, rfl⟩ := h f hf
  exact q.mul_mem_right c hpq

/-- Hartogs extension: an element of the fraction field which becomes integral after
multiplication by a power of every nonzero element of the maximal ideal is integral, provided
some nonzero prime lies strictly below the maximal ideal. -/
theorem exists_eq_of_forall_pow_mul {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    {q : Ideal O} (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hqm : q ≠ IsLocalRing.maximalIdeal O)
    (x : K) (hx : ∀ f ∈ IsLocalRing.maximalIdeal O, f ≠ 0 →
      ∃ (k : ℕ) (a : O), algebraMap O K f ^ k * x = algebraMap O K a) :
    ∃ a : O, algebraMap O K a = x := by
  obtain ⟨a, b, hab, rfl⟩ := IsFractionRing.exists_reduced_fraction O x
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  by_cases hb : IsUnit (b : O)
  · obtain ⟨u, hu⟩ := hb
    refine ⟨a * ↑u⁻¹, ?_⟩
    symm
    rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← hu, mul_assoc, Units.inv_mul, mul_one]
  · obtain ⟨p, hpirr, hpb⟩ := WfDvdMonoid.exists_irreducible_factor hb hb0
    have hp : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr
    obtain ⟨f, hfm, hpf⟩ := exists_mem_maximalIdeal_not_dvd hq hq0 hqm hp
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hpf (dvd_zero p)
    obtain ⟨k, c, hc⟩ := hx f hfm hf0
    have hmul : algebraMap O K (f ^ k * a) = algebraMap O K (c * b) := by
      rw [map_mul, map_mul, map_pow, ← IsLocalization.mk'_spec K a b, ← mul_assoc, hc]
    have heq : f ^ k * a = c * b := IsFractionRing.injective O K hmul
    have hpa : p ∣ a := by
      have h1 : p ∣ f ^ k * a := by
        rw [heq]
        exact dvd_mul_of_dvd_right hpb c
      rcases hp.dvd_or_dvd h1 with h2 | h2
      · exact absurd (hp.dvd_of_dvd_pow h2) hpf
      · exact h2
    exact absurd (hab hpa hpb) hp.not_isUnit

end Langlands.CommutativeAlgebra.FactorialLocalHartogs
