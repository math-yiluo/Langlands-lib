import Langlands.CommutativeAlgebra.RegularLocalDomainProof
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-! # Elementary tools for factoriality of regular local rings -/

universe u

open IsLocalRing

namespace Langlands.CommutativeAlgebra.RegularLocalFactorial

variable {R : Type u} [CommRing R]

/-- Killing an element of `𝔪 \ 𝔪²` in a regular local ring preserves regularity. -/
theorem isRegularLocalRing_quotient_span_singleton [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  have hxtop : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal x).mp hx
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdrop := RegularLocalDomain.spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hreg : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdim : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    have := Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal R) hx
    rwa [maximalIdeal_height_eq_ringKrullDim] at this
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial :
      ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊥)
  rw [← hd, ← hreg] at hdim
  rw [← hd]
  have h1 : (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : ℕ∞) ≤
      d + 1 := by
    have := (Nat.cast_le (α := WithBot ℕ∞)).mpr hdrop
    exact_mod_cast this.trans hdim
  have h2 : ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : ℕ∞) ≤ d := by
    push_cast at h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1
  exact_mod_cast h2

/-- The embedding dimension drops by exactly one when a regular parameter is killed. -/
theorem spanFinrank_quotient_add_one [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    letI : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      isRegularLocalRing_quotient_span_singleton hx hx2
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
      (maximalIdeal R).spanFinrank := by
  have := isRegularLocalRing_quotient_span_singleton hx hx2
  have hdrop := RegularLocalDomain.spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hdim := Ideal.height_le_ringKrullDim_quotient_add_one (p := maximalIdeal R) hx
  rw [maximalIdeal_height_eq_ringKrullDim,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})] at hdim
  have hback : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    exact_mod_cast hdim
  exact le_antisymm hdrop hback

/-- Every element of `𝔪 \ 𝔪²` in a regular local ring is prime. -/
theorem prime_of_mem_maximalIdeal_notMem_sq [IsRegularLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    Prime x := by
  have := isRegularLocalRing_quotient_span_singleton hx hx2
  have := regularLocalDomain (R ⧸ Ideal.span {x}) inferInstance
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Ideal.zero_mem _)
  exact (Ideal.span_singleton_prime hx0).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)

/-- A positive-dimensional regular local ring has a regular parameter. -/
theorem exists_prime_parameter [IsRegularLocalRing R]
    (hn : (maximalIdeal R).spanFinrank ≠ 0) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ Prime x := by
  have hnot : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
    intro h
    have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
      simpa [smul_eq_mul, pow_two] using h
    have hm : maximalIdeal R = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing hle (maximalIdeal_le_jacobson _)
    exact hn (by simp [hm])
  obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hnot
  exact ⟨x, hx, hx2, prime_of_mem_maximalIdeal_notMem_sq hx hx2⟩

/-- Regular local rings of embedding dimension at most one are principal ideal rings. -/
theorem isPrincipalIdealRing_of_spanFinrank_le_one [IsRegularLocalRing R]
    (hn : (maximalIdeal R).spanFinrank ≤ 1) : IsPrincipalIdealRing R := by
  have := regularLocalDomain R inferInstance
  rcases Nat.eq_zero_or_pos (maximalIdeal R).spanFinrank with h0 | hpos
  · have hm : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊤
    · exact ⟨1, by simp [hI]⟩
    · have hIbot : I = ⊥ := le_bot_iff.mp (hm ▸ IsLocalRing.le_maximalIdeal hI)
      exact ⟨0, by simp [hIbot]⟩
  · have h1 : (maximalIdeal R).spanFinrank = 1 := by omega
    have hc : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      exact h1
    have : IsDiscreteValuationRing R := finrank_CotangentSpace_eq_one_iff.mp hc
    infer_instance

/-- The zero- and one-dimensional cases of regular-local factoriality. -/
theorem uniqueFactorizationMonoid_of_ringKrullDim_le_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≤ 1) : UniqueFactorizationMonoid R := by
  have := regularLocalDomain R inferInstance
  have hn : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hdim
    exact_mod_cast hdim
  have := isPrincipalIdealRing_of_spanFinrank_le_one hn
  infer_instance

/-- In a Noetherian domain it is enough to show that every height-one prime is principal. -/
theorem uniqueFactorizationMonoid_of_height_one_principal [IsDomain R] [IsNoetherianRing R]
    (H : ∀ (P : Ideal R), P.IsPrime → P.height = 1 → P.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  apply UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr
  intro P hP hPprime
  have := hPprime
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem P).mpr haP)
  have := hQ.isPrime
  have hQbot : Q ≠ ⊥ := by
    intro hbot
    have haQ : a ∈ Q := hQ.le (Ideal.mem_span_singleton_self a)
    exact ha0 (by simpa [hbot] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) Q hQ)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hQbot))
  have := H Q hQ.isPrime hQ1
  obtain ⟨b, hb⟩ := (H Q hQ.isPrime hQ1).principal
  change Q = Ideal.span {b} at hb
  have hb0 : b ≠ 0 := by
    intro h0
    exact hQbot (by simpa [h0] using hb)
  have hbQ : b ∈ Q := by rw [hb]; exact Ideal.mem_span_singleton_self b
  refine ⟨b, hQP hbQ, (Ideal.span_singleton_prime hb0).mp ?_⟩
  rw [← hb]
  exact hQ.isPrime

end Langlands.CommutativeAlgebra.RegularLocalFactorial
