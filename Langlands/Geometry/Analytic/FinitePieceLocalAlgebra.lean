import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Commutative algebra for the local comparison on finite pieces -/

noncomputable section

namespace Langlands.Analytic.FinitePieceLocalAlgebra

open Polynomial

section Krull

variable {C S : Type*} [CommRing C] [CommRing S]

/-- If a surjective ring map out of a Noetherian ring has kernel inside every power of the
inverse image of every maximal ideal, then it becomes bijective after localizing at the
inverse image of any prime ideal. -/
theorem bijective_localRingHom_of_ker_le_pow [IsNoetherianRing C] (χ : C →+* S)
    (hχ : Function.Surjective χ)
    (hker : ∀ n : Ideal S, n.IsMaximal → ∀ k : ℕ, RingHom.ker χ ≤ (n.comap χ) ^ k)
    (𝔰 : Ideal S) [𝔰.IsPrime] :
    Function.Bijective (Localization.localRingHom (𝔰.comap χ) 𝔰 χ rfl) := by
  constructor
  · obtain ⟨n, hn, h𝔰n⟩ := Ideal.exists_le_maximal 𝔰 (Ideal.IsPrime.ne_top inferInstance)
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝔰.comap χ).primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htc⟩ := hx
    obtain ⟨t', rfl⟩ := hχ t
    have hmem : t' * c ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker, map_mul]
      exact htc
    have hinf : t' * c ∈ (⨅ i : ℕ, (n.comap χ) ^ i • ⊤ : Submodule C C) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [smul_eq_mul, Ideal.mul_top]
      exact hker n hn i hmem
    obtain ⟨⟨r, hr⟩, hrc⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (n.comap χ) (t' * c)).1 hinf
    rw [IsLocalization.mk'_eq_zero_iff]
    have hr1 : 1 - r ∈ (𝔰.comap χ).primeCompl := by
      intro h
      have h1 : 1 - r ∈ n.comap χ := Ideal.comap_mono h𝔰n h
      have : (1 : C) ∈ n.comap χ := by
        simpa using (n.comap χ).add_mem h1 hr
      exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 this)
    refine ⟨⟨(1 - r) * t', (𝔰.comap χ).primeCompl.mul_mem hr1 ht⟩, ?_⟩
    change (1 - r) * t' * c = 0
    have : r * (t' * c) = t' * c := hrc
    calc (1 - r) * t' * c = t' * c - r * (t' * c) := by ring
      _ = 0 := by rw [this, sub_self]
  · intro y
    obtain ⟨⟨z, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔰.primeCompl y
    obtain ⟨c, rfl⟩ := hχ z
    obtain ⟨⟨s, hs⟩, hsu⟩ : ∃ s : (𝔰.comap χ).primeCompl, χ s = u := by
      obtain ⟨s, hs⟩ := hχ u
      exact ⟨⟨s, fun h => u.2 (hs ▸ h)⟩, hs⟩
    refine ⟨IsLocalization.mk' _ c ⟨s, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hsu

end Krull

section Integral

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

/-- If every element of `C` satisfies a monic polynomial over `R` modulo an ideal `I`, then
every quotient by a power of `I` is integral over `R`. -/
theorem isIntegral_quotient_pow (I : Ideal C)
    (hI : ∀ x : C, ∃ f : R[X], f.Monic ∧ aeval x f ∈ I) (k : ℕ) :
    Algebra.IsIntegral R (C ⧸ I ^ k) := by
  constructor
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨f, hf, hfx⟩ := hI x
  refine ⟨f ^ k, hf.pow k, ?_⟩
  rw [← aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, map_pow,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hfx k

/-- Under the same hypothesis, quotients of a finite-type algebra by powers of `I` are
finite modules. -/
theorem finite_quotient_pow [Algebra.FiniteType R C] (I : Ideal C)
    (hI : ∀ x : C, ∃ f : R[X], f.Monic ∧ aeval x f ∈ I) (k : ℕ) :
    Module.Finite R (C ⧸ I ^ k) := by
  have := isIntegral_quotient_pow I hI k
  have : Algebra.FiniteType R (C ⧸ I ^ k) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (I ^ k))
      (Ideal.Quotient.mkₐ_surjective R (I ^ k))
  exact Algebra.IsIntegral.finite

/-- An algebra map to a module-finite algebra makes every element integral modulo any ideal
containing its kernel. -/
theorem exists_monic_aeval_mem_of_ker_le {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] (χ : C →ₐ[R] S) (I : Ideal C) (hI : RingHom.ker χ ≤ I) (x : C) :
    ∃ f : R[X], f.Monic ∧ aeval x f ∈ I := by
  have : Algebra.IsIntegral R S := inferInstance
  obtain ⟨f, hf, hfx⟩ := Algebra.IsIntegral.isIntegral (R := R) (χ x)
  refine ⟨f, hf, hI ?_⟩
  rw [RingHom.mem_ker]
  change χ (aeval x f) = 0
  rw [← aeval_algHom_apply, aeval_def]
  exact hfx

end Integral

section Units

variable {C T : Type*} [CommRing C] [CommRing T]

/-- An element of `C ⧸ p ^ k`, with `p` the inverse image of an ideal `J`, whose image in
`T ⧸ J` is `1` is a unit. -/
theorem isUnit_of_lift_eq_one (χ : C →+* T) (J : Ideal T) (k : ℕ)
    (h : ∀ x ∈ (J.comap χ) ^ k, (Ideal.Quotient.mk J).comp χ x = 0)
    (z : C ⧸ (J.comap χ) ^ k)
    (hz : Ideal.Quotient.lift ((J.comap χ) ^ k) ((Ideal.Quotient.mk J).comp χ) h z = 1) :
    IsUnit z := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, ← map_one (Ideal.Quotient.mk J),
    Ideal.Quotient.eq, ← map_one χ, ← map_sub] at hz
  have hnil : IsNilpotent (Ideal.Quotient.mk ((J.comap χ) ^ k) x - 1) := by
    refine ⟨k, ?_⟩
    rw [← map_one (Ideal.Quotient.mk ((J.comap χ) ^ k)), ← map_sub, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_comap.2 hz) k
  have := hnil.isUnit_add_one
  rwa [sub_add_cancel] at this

/-- The lift used in `isUnit_of_lift_eq_one` is well defined. -/
theorem lift_pow_comap_aux (χ : C →+* T) (J : Ideal T) (k : ℕ) (hk : k ≠ 0) :
    ∀ x ∈ (J.comap χ) ^ k, (Ideal.Quotient.mk J).comp χ x = 0 := by
  intro x hx
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
  exact Ideal.pow_le_self hk hx

end Units

end Langlands.Analytic.FinitePieceLocalAlgebra
