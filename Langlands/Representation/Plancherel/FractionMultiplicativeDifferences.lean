import Mathlib.RingTheory.Localization.NumDen

/-! # Prime divisibility and multiplicative differences of fractions -/

noncomputable section

namespace Langlands.Plancherel

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The quotient of a translated fraction by the original fraction. -/
def fractionMultiplicativeDifference (σ : R ≃+* R) (f : K) : K :=
  (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K) f / f

/-- All iterated differences, taking one translation from each successive
set in the list, equal one. The empty iteration gives the original fraction. -/
def MultiplicativeDifferencesVanish : List (Set (R ≃+* R)) → K → Prop
  | [], f => f = 1
  | S :: rest, f => ∀ σ ∈ S, MultiplicativeDifferencesVanish rest (fractionMultiplicativeDifference σ f)

omit [IsDomain R] in
/-- Explicit numerator and denominator for the multiplicative difference. -/
theorem fractionMultiplicativeDifference_div (σ : R ≃+* R) (a b : R) :
    fractionMultiplicativeDifference σ (algebraMap R K a / algebraMap R K b) =
      algebraMap R K (σ a * b) / algebraMap R K (σ b * a) := by
  simp only [fractionMultiplicativeDifference, map_div₀,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_mul, div_div_div_eq]

private theorem not_vanish_of_prime_avoidance
    (p : R) (hp : Prime p) (sets : List (Set (R ≃+* R)))
    (havoid : ∀ S ∈ sets, ∀ c : R, c ≠ 0 → ∃ σ ∈ S, ¬p ∣ σ c)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (p ∣ a ∧ ¬p ∣ b) ∨ (p ∣ b ∧ ¬p ∣ a)) :
    ¬ MultiplicativeDifferencesVanish sets (algebraMap R K a / algebraMap R K b) := by
  induction sets generalizing a b with
  | nil =>
      intro hvanish
      change algebraMap R K a / algebraMap R K b = 1 at hvanish
      have hb' : algebraMap R K b ≠ 0 := fun h0 =>
        hb (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
      have hab : a = b := IsFractionRing.injective R K
        (by simpa only [one_mul] using (div_eq_iff hb').mp hvanish)
      subst b
      exact h.elim (fun hc => hc.2 hc.1) (fun hc => hc.2 hc.1)
  | cons S rest ih =>
      intro hvanish
      obtain ⟨σ, hσ, hpσ⟩ := havoid S List.mem_cons_self (a * b) (mul_ne_zero ha hb)
      have hpσa : ¬ p ∣ σ a := fun hd => hpσ (by rw [map_mul]; exact dvd_mul_of_dvd_left hd _)
      have hpσb : ¬ p ∣ σ b := fun hd => hpσ (by rw [map_mul]; exact dvd_mul_of_dvd_right hd _)
      have hσa : σ a ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr ha
      have hσb : σ b ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hb
      have hnext : (p ∣ σ a * b ∧ ¬p ∣ σ b * a) ∨ (p ∣ σ b * a ∧ ¬p ∣ σ a * b) := by
        rcases h with h | h
        · exact Or.inr ⟨dvd_mul_of_dvd_right h.1 _, fun hd => (hp.dvd_mul.mp hd).elim hpσa h.2⟩
        · exact Or.inl ⟨dvd_mul_of_dvd_right h.1 _, fun hd => (hp.dvd_mul.mp hd).elim hpσb h.2⟩
      have hs := hvanish σ hσ
      rw [fractionMultiplicativeDifference_div] at hs
      exact ih (fun S hS => havoid S (List.mem_cons_of_mem _ hS)) _ _
        (mul_ne_zero hσa hb) (mul_ne_zero hσb ha) hnext hs

/-- A prime dividing exactly one side of a fraction whose iterated
multiplicative differences vanish divides every translate of some nonzero
regular element for at least one of the translation sets. -/
theorem exists_translationSet_prime_dvd_every_translate
    (p : R) (hp : Prime p) (sets : List (Set (R ≃+* R)))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (p ∣ a ∧ ¬p ∣ b) ∨ (p ∣ b ∧ ¬p ∣ a))
    (hvanish : MultiplicativeDifferencesVanish sets (algebraMap R K a / algebraMap R K b)) :
    ∃ S ∈ sets, ∃ c : R, c ≠ 0 ∧ ∀ σ ∈ S, p ∣ σ c := by
  by_contra! hn
  exact not_vanish_of_prime_avoidance p hp sets hn a b ha hb h hvanish

end Langlands.Plancherel
