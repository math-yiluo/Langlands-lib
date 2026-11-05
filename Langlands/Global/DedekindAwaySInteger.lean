import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.Localization.Submodule

noncomputable section

universe u v

open IsDedekindDomain

namespace Langlands.Global

variable {A : Type u} {K : Type v} [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K] (t : A) (ht : t ≠ 0)

/-- Away localization inside the original fraction field, retaining the original embedding. -/
def dedekindAwaySubalgebra : Subalgebra A K :=
  Localization.subalgebra.ofField K (Submonoid.powers t)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht)

/-- Inverting one element removes precisely its original height-one primes. -/
theorem mem_dedekindAwaySubalgebra_iff (x : K) :
    x ∈ dedekindAwaySubalgebra t ht ↔
      ∀ P : HeightOneSpectrum A, t ∉ P.asIdeal → P.valuation K x ≤ 1 := by
  constructor
  · rintro ⟨a, b, hb, rfl⟩ P hP
    obtain ⟨n, rfl⟩ := hb
    rw [map_mul, map_inv₀, map_pow, map_pow,
      (P.valuation_eq_one_iff_notMem).mpr hP, one_pow, inv_one, mul_one]
    exact P.valuation_le_one a
  · intro hx
    let D := dedekindAwaySubalgebra (K := K) t ht
    let : IsLocalization (Submonoid.powers t) D :=
      Localization.subalgebra.isLocalization_ofField K _ _
    let : IsDedekindDomain D := IsLocalization.isDedekindDomain A
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht) D
    have hlocal : x ∈ (⊥ : Subalgebra D K) := by
      rw [← HeightOneSpectrum.iInf_localization_eq_bot D, Algebra.mem_iInf]
      intro Q
      have hP0 : Q.asIdeal.under A ≠ ⊥ := by
        intro h
        have hm := IsLocalization.map_under (Submonoid.powers t) D Q.asIdeal
        rw [h, Ideal.map_bot] at hm
        exact Q.ne_bot hm.symm
      let P : HeightOneSpectrum A := ⟨Q.asIdeal.under A, inferInstance, hP0⟩
      have htP : t ∉ P.asIdeal :=
        Ideal.notMem_of_isUnit Q.asIdeal
          (IsLocalization.map_units D (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t))
      have hle : HeightOneSpectrum.valuationSubringAtPrime K P ≤
          (Q.valuation K).valuationSubring := by
        rintro y ⟨a, b, hb, rfl⟩
        change Q.valuation K (algebraMap A K a * (algebraMap A K b)⁻¹) ≤ 1
        rw [map_mul, map_inv₀, IsScalarTower.algebraMap_apply A D K b,
          (Q.valuation_eq_one_iff_notMem).mpr hb, inv_one, mul_one,
          IsScalarTower.algebraMap_apply A D K a]
        exact Q.valuation_le_one _
      have heq : HeightOneSpectrum.valuationSubringAtPrime K P =
          (Q.valuation K).valuationSubring :=
        ValuationSubring.eq_of_le_of_ne_top _ hle (by
          simpa only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not] using
            (inferInstance : Q.valuation K |>.IsNontrivial))
      change x ∈ HeightOneSpectrum.valuationSubringAtPrime K Q
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, ← heq,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hx P htP
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hlocal
    exact ha ▸ a.property

/-- The actual localization is the actual integer ring outside the primes dividing its denominator. -/
theorem dedekindAwaySubalgebra_eq_integer :
    dedekindAwaySubalgebra (K := K) t ht =
      ({P : HeightOneSpectrum A | t ∈ P.asIdeal} : Set (HeightOneSpectrum A)).integer K := by
  ext x
  exact mem_dedekindAwaySubalgebra_iff t ht x

/-- The original away-localization and outside-prime integer constructions agree elementwise. -/
def dedekindAwaySIntegerEquiv :
    dedekindAwaySubalgebra (K := K) t ht ≃ₐ[A]
      ({P : HeightOneSpectrum A | t ∈ P.asIdeal} : Set (HeightOneSpectrum A)).integer K :=
  Subalgebra.equivOfEq _ _ (dedekindAwaySubalgebra_eq_integer t ht)

@[simp]
theorem dedekindAwaySIntegerEquiv_coe (x : dedekindAwaySubalgebra (K := K) t ht) :
    (dedekindAwaySIntegerEquiv t ht x : K) = x := rfl

end Langlands.Global
