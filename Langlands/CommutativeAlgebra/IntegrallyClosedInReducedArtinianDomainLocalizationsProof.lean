import Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinianDomainLocalizationsStatement
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic

/-! # Proof: domain prime localizations of rings integrally closed in reduced Artinian rings -/

namespace Langlands.CommutativeAlgebra

namespace IntegrallyClosedInReducedArtinian

/-- An idempotent is a root of the monic polynomial `X ^ 2 - X`, hence integral. -/
theorem isIntegral_of_isIdempotentElem {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral R e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub
      (Polynomial.degree_X_le.trans_lt (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)))
  · simp [sq, he.eq]

/-- In a reduced Artinian ring, if `a * b = 0` then some idempotent `e` satisfies
`e * b = 0` and `(1 - e) * a = 0`: take `e` to be the support idempotent of `a` in
the decomposition as a finite product of fields. -/
theorem exists_separating_idempotent {B : Type*} [CommRing B] [IsReduced B]
    [IsArtinianRing B] {a b : B} (h : a * b = 0) :
    ∃ e : B, IsIdempotentElem e ∧ e * b = 0 ∧ (1 - e) * a = 0 := by
  classical
  let φ := IsArtinianRing.equivPi B
  have hab : ∀ m, φ a m * φ b m = 0 := fun m => by
    rw [← Pi.mul_apply, ← map_mul, h, map_zero, Pi.zero_apply]
  refine ⟨φ.symm (fun m => if φ a m = 0 then 0 else 1), ?_, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply]
    funext m
    simp only [Pi.mul_apply]
    split_ifs <;> simp
  · apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
    funext m
    simp only [Pi.mul_apply, Pi.zero_apply]
    split_ifs with hm
    · simp
    · have : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
      simpa [hm] using hab m
  · apply φ.injective
    rw [map_mul, map_sub, map_one, AlgEquiv.apply_symm_apply, map_zero]
    funext m
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    split_ifs with hm <;> simp [hm]

end IntegrallyClosedInReducedArtinian

open IntegrallyClosedInReducedArtinian in
/-- If `R` is integrally closed in a reduced Artinian ring, then every prime
localization of `R` is a domain. -/
theorem integrallyClosedInReducedArtinianDomainLocalizations.{u, v} :
    IntegrallyClosedInReducedArtinianDomainLocalizations.{u, v} := by
  intro R B _ _ _ hic hred hart p hp
  have hinj : Function.Injective (algebraMap R B) :=
    IsIntegralClosure.algebraMap_injective R R B
  -- Idempotents of `B` descend to `R` and separate the factors of a zero product.
  have key : ∀ a b : R, a * b = 0 →
      ∃ r : R, IsIdempotentElem r ∧ r * b = 0 ∧ (1 - r) * a = 0 := by
    intro a b hab
    obtain ⟨e, he, heb, hea⟩ := exists_separating_idempotent (B := B)
      (a := algebraMap R B a) (b := algebraMap R B b) (by rw [← map_mul, hab, map_zero])
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := R) (A := B)
      (isIntegral_of_isIdempotentElem he)
    refine ⟨r, ?_, ?_, ?_⟩
    · apply hinj
      rw [map_mul, hr]
      exact he
    · apply hinj
      rw [map_mul, hr, map_zero]
      exact heb
    · apply hinj
      rw [map_mul, map_sub, map_one, hr, map_zero]
      exact hea
  have : NoZeroDivisors (Localization.AtPrime p) := by
    constructor
    intro x y hxy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hxy
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨r, -, hrb, hra⟩ := key (u * a) b (by rw [mul_assoc]; exact hu)
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
        (algebraMap R (Localization.AtPrime p) r) with h | h
    · right
      have hb : algebraMap R (Localization.AtPrime p) b = 0 := by
        have := congrArg (algebraMap R (Localization.AtPrime p)) hrb
        rw [map_mul, map_zero] at this
        exact (h.mul_right_eq_zero).mp this
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ b).mp hb
      exact (IsLocalization.mk'_eq_zero_iff b t).mpr ⟨m, hm⟩
    · left
      have ha : algebraMap R (Localization.AtPrime p) (u * a) = 0 := by
        have := congrArg (algebraMap R (Localization.AtPrime p)) hra
        rw [map_mul, map_sub, map_one, map_zero] at this
        exact (h.mul_right_eq_zero).mp this
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ (u * a)).mp ha
      exact (IsLocalization.mk'_eq_zero_iff a s).mpr ⟨m * u, by rw [Submonoid.coe_mul, mul_assoc]; exact hm⟩
  exact NoZeroDivisors.to_isDomain _

end Langlands.CommutativeAlgebra
