import Langlands.Global.Arithmetic.CyclotomicSymbol
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-! # Norms of ideals prime to `m` lie in the Galois image

For a Galois extension `L / K` of number fields containing a primitive `m`-th root of unity
`ζ`, the arithmetic Frobenius at a prime `P ∤ m` of `𝓞 K` acts on `ζ` as `ζ ↦ ζ^{N(P)}`. Hence
the class of `N(P)` in `(ℤ/m)ˣ` lies in the image of `Gal(L/K)`. Multiplicatively, the
product of the cyclotomic symbols outside a finite set of primes containing those dividing
`m`, evaluated at the absolute norm of a nonzero ideal, lies in that image.
-/

noncomputable section

open NumberField

namespace Langlands.Global.CyclotomicSymbol

section Frobenius

variable (K : Type*) {L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)

/-- The image of `Gal(L/K)` in `(ℤ/m)ˣ` through its action on `ζ`. -/
def galoisImage : Subgroup (ZMod m)ˣ := (hζ.autToPow K).range

/-- The arithmetic Frobenius at a prime `P ∤ m` acts on `ζ` as `ζ ↦ ζ ^ N(P)`. -/
theorem exists_autToPow_eq_card (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (hm : ((m : ℕ) : 𝓞 K) ∉ P) :
    ∃ σ : Gal(L/K), ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m) = Nat.card (𝓞 K ⧸ P) := by
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 L))
    (by rw [Ideal.under_bot]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hP
    rw [← hQP, h, Ideal.under_bot]
  have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) Gal(L/K) Q
  let ζ' : 𝓞 L := ⟨ζ, hζ.isIntegral (NeZero.pos m)⟩
  have hζ' : ζ' ^ m = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  have hmQ : ((m : ℕ) : 𝓞 L) ∉ Q := by
    intro h
    apply hm
    rw [← hQP, Ideal.mem_comap, map_natCast]
    exact h
  have h1 := hσ.apply_of_pow_eq_one hζ' hmQ
  rw [hQP] at h1
  have h2 : σ ζ = ζ ^ Nat.card (𝓞 K ⧸ P) := by
    have h3 := congrArg (algebraMap (𝓞 L) L) h1
    rw [map_pow] at h3
    exact h3
  refine ⟨σ, ?_⟩
  have h4 := hζ.autToPow_spec K σ
  rw [h2, ← pow_mod_orderOf, ← pow_mod_orderOf (n := Nat.card (𝓞 K ⧸ P)),
    ← hζ.eq_orderOf] at h4
  have h5 := hζ.pow_inj (Nat.mod_lt _ (NeZero.pos m)) (Nat.mod_lt _ (NeZero.pos m)) h4
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m)]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 h5

omit [NeZero m] in
/-- The norm of a nonzero prime is coprime to `m` when `m ∉ P`. -/
theorem coprime_card_of_not_mem (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (hm : ((m : ℕ) : 𝓞 K) ∉ P) : Nat.Coprime (Nat.card (𝓞 K ⧸ P)) m := by
  have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP
  have := Fintype.ofFinite (𝓞 K ⧸ P)
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))
  rw [Nat.card_eq_fintype_card, hcard]
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdvd => hm ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P)) m).2 hdvd

/-- The class of `N(P)` lies in the Galois image for a nonzero prime `P ∤ m`. -/
theorem unitOfCoprime_card_mem (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥)
    (hm : ((m : ℕ) : 𝓞 K) ∉ P) :
    ZMod.unitOfCoprime _ (coprime_card_of_not_mem K P hP hm) ∈ galoisImage K hζ := by
  obtain ⟨σ, hσ⟩ := exists_autToPow_eq_card K hζ P hP hm
  exact ⟨σ, Units.ext (by rw [hσ, ZMod.coe_unitOfCoprime])⟩

end Frobenius

section Outside

instance infinite_ringOfIntegers (K : Type*) [Field K] [NumberField K] : Infinite (𝓞 K) :=
  Infinite.of_injective (Int.cast : ℤ → 𝓞 K) Int.cast_injective

variable (m : ℕ) [NeZero m] (T : Finset ℕ)

/-- A nonzero natural number as a rational unit. -/
def natUnit (n : ℕ) (hn : n ≠ 0) : ℚˣ := Units.mk0 (n : ℚ) (Nat.cast_ne_zero.2 hn)

theorem natUnit_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    natUnit (a * b) (mul_ne_zero ha hb) = natUnit a ha * natUnit b hb :=
  Units.ext (by simp [natUnit])

theorem natUnit_one : natUnit 1 one_ne_zero = 1 := Units.ext (by simp [natUnit])

theorem mulSupport_outside_subset (α : ℚˣ) :
    (Function.mulSupport fun p : Nat.Primes => if (p : ℕ) ∈ T then 1 else primeSymbol m p α) ⊆
      Function.mulSupport fun p : Nat.Primes => primeSymbol m p α := by
  intro p hp
  have hp' : (if (p : ℕ) ∈ T then 1 else primeSymbol m p α) ≠ 1 := hp
  change primeSymbol m p α ≠ 1
  by_cases h : (p : ℕ) ∈ T
  · rw [ite_eq_left h] at hp'
    exact absurd rfl hp'
  · rwa [ite_eq_right h] at hp'

/-- The product of the local symbols at the primes outside `T`. -/
def outsideSymbol : ℚˣ →* (ZMod m)ˣ where
  toFun α := ∏ᶠ p : Nat.Primes, if (p : ℕ) ∈ T then 1 else primeSymbol m p α
  map_one' := by simp
  map_mul' a b := by
    rw [← finprod_mul_distrib ((mulSupport_primeSymbol_finite m a).subset
      (mulSupport_outside_subset m T a)) ((mulSupport_primeSymbol_finite m b).subset
      (mulSupport_outside_subset m T b))]
    congr 1
    funext p
    by_cases h : (p : ℕ) ∈ T
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, one_mul]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, map_mul]

theorem outsideSymbol_apply (α : ℚˣ) :
    outsideSymbol m T α = ∏ᶠ p : Nat.Primes, if (p : ℕ) ∈ T then 1 else primeSymbol m p α :=
  rfl

/-- Outside `T ⊇ {primes dividing m}`, the local symbol is `ℓ ^ v_ℓ`. -/
theorem primeSymbol_of_not_mem (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∈ T) (p : Nat.Primes)
    (hp : (p : ℕ) ∉ T) (α : ℚˣ) :
    primeSymbol m p α = ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd p.2).2
      fun h => hp (hT p p.2 h)) ^ padicValRat p α := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  change ratLocalSymbol m p α = _
  rw [ratLocalSymbol, MonoidHom.comp_apply, localSymbol_of_not_dvd m p
    (fun h => hp (hT p p.2 h)), valuation_ratCast_unit]

theorem outsideSymbol_primePow (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∈ T) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (f : ℕ) :
    outsideSymbol m T (natUnit (ℓ ^ f) (pow_ne_zero _ hℓ.ne_zero)) =
      if hT' : ℓ ∈ T then 1 else ZMod.unitOfCoprime (ℓ ^ f) (Nat.Coprime.pow_left _
        ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun h => hT' (hT ℓ hℓ h))) := by
  have hval : ∀ p : Nat.Primes, padicValRat p ((natUnit (ℓ ^ f) (pow_ne_zero _ hℓ.ne_zero) : ℚˣ) :
      ℚ) = if (p : ℕ) = ℓ then (f : ℤ) else 0 := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have : Fact ℓ.Prime := ⟨hℓ⟩
    rw [natUnit, Units.val_mk0, Nat.cast_pow, padicValRat.pow, padicValRat.of_nat]
    split_ifs with h
    · subst h
      rw [padicValNat_self, Nat.cast_one, mul_one]
    · rw [padicValNat_primes h, Nat.cast_zero, mul_zero]
  let ℓ' : Nat.Primes := ⟨ℓ, hℓ⟩
  rw [outsideSymbol_apply, finprod_eq_single _ ℓ']
  · by_cases hT' : ℓ ∈ T
    · rw [dite_eq_left hT']
      exact ite_eq_left hT'
    · rw [dite_eq_right hT']
      change (if ℓ ∈ T then 1 else primeSymbol m ℓ' _) = _
      rw [ite_eq_right hT', primeSymbol_of_not_mem m T hT ℓ' hT', hval, ite_eq_left rfl]
      apply Units.ext
      simp [ℓ']
  · intro p hp
    by_cases h : (p : ℕ) ∈ T
    · exact ite_eq_left h
    · rw [ite_eq_right h, primeSymbol_of_not_mem m T hT p h, hval,
        ite_eq_right fun h' => hp (Subtype.ext h'), zpow_zero]

variable (K : Type*) {L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)

/-- The product of the local symbols outside `T` at the absolute norm of a nonzero ideal of
`𝓞 K` lies in the Galois image, when `T` contains every prime dividing `m`. -/
theorem outsideSymbol_absNorm_mem (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∈ T)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    outsideSymbol m T (natUnit (Ideal.absNorm I) (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h))) ∈
      galoisImage K hζ := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd Ideal.zero_eq_bot hI
  | h₂ x hx =>
    have hx' : x = ⊤ := Ideal.isUnit_iff.1 hx
    subst hx'
    have h1 : natUnit (Ideal.absNorm (⊤ : Ideal (𝓞 K)))
        (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) = 1 :=
      Units.ext (by simp [natUnit])
    rw [h1, map_one]
    exact Subgroup.one_mem _
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hP
    have hna : Ideal.absNorm a ≠ 0 := fun h => ha (Ideal.absNorm_eq_zero_iff.1 h)
    have hnP : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hsplit : natUnit (Ideal.absNorm (P * a)) (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) =
        natUnit (Ideal.absNorm P) hnP * natUnit (Ideal.absNorm a) hna :=
      Units.ext (by simp [natUnit])
    rw [hsplit, map_mul]
    refine Subgroup.mul_mem _ ?_ (ih ha)
    -- the prime factor
    have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hP0
    let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    have : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have := Fintype.ofFinite (𝓞 K ⧸ P)
    obtain ⟨f, hℓ, hcard⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))
    have hnorm : Ideal.absNorm P = ringChar (𝓞 K ⧸ P) ^ (f : ℕ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
    have heq : natUnit (Ideal.absNorm P) hnP =
        natUnit (ringChar (𝓞 K ⧸ P) ^ (f : ℕ)) (pow_ne_zero _ hℓ.ne_zero) :=
      Units.ext (by simp [natUnit, hnorm])
    rw [heq, outsideSymbol_primePow m T hT hℓ]
    split_ifs with hT'
    · exact Subgroup.one_mem _
    · have hm : ((m : ℕ) : 𝓞 K) ∉ P := by
        intro hmem
        apply hT'
        apply hT _ hℓ
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
        exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P)) m).1 hmem
      have hmem := unitOfCoprime_card_mem K hζ P hP0 hm
      convert hmem using 1
      apply Units.ext
      simp [Nat.card_eq_fintype_card, hcard]

end Outside

end Langlands.Global.CyclotomicSymbol
