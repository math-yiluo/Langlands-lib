import Langlands.Global.Arithmetic.LocalPowerDescent

/-! # Almost-everywhere local powers imply global half-powers -/

universe u

namespace Langlands.Global

open NumberField IsDedekindDomain Filter

/-- **Artin–Tate IX.1 Theorem 1, half-power form.** A global unit that is a `(2 * n)`-th power in
the completion at every finite place outside a finite set is a global `n`-th power. -/
theorem almostEverywherePowerHalfStatement : AlmostEverywherePowerHalfStatement.{u} := by
  apply Arithmetic.PowerDescent.almostEverywherePowerHalf_of_prime_powers
  intro K _ _ S p r hp hr a ha
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ c : v.adicCompletion K, c ^ (2 * p ^ r) = algebraMap K (v.adicCompletion K) a :=
    S.eventually_cofinite_notMem.mono fun v hv => by
      obtain ⟨b, hb⟩ := ha v hv
      exact ⟨b, by simpa using congrArg Units.val hb⟩
  apply (Arithmetic.PowerDescent.exists_unit_pow_eq_iff _ _).2
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := Nat.exists_eq_succ_of_ne_zero hr.ne'
    refine Arithmetic.LocalPowerDescent.exists_pow_eq_of_eventually_twoPow s a.ne_zero
      (hev.mono fun v ⟨c, hc⟩ => ⟨c, ?_⟩)
    rw [show 2 ^ (s + 2) = 2 * 2 ^ (s + 1) by ring]
    exact hc
  · exact Arithmetic.LocalPowerDescent.exists_pow_eq_of_eventually_oddPrimePow hp hp2 r a.ne_zero
      (hev.mono fun v ⟨c, hc⟩ => ⟨c ^ 2, by rw [← pow_mul, hc]⟩)

end Langlands.Global
