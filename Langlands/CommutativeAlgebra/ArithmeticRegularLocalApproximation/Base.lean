import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.RegularAlgebra
import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Presentation
import Mathlib.RingTheory.Flat.TorsionFree

/-! # The prime subring of a discrete valuation ring as a regular base -/

universe u w

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation

variable {Λ : Type u} [CommRing Λ]

/-- Every element of the smallest subring is an integer. -/
theorem intCast_surjective_bot : Function.Surjective (Int.castRingHom (⊥ : Subring Λ)) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hx
  exact ⟨n, Subtype.ext (by simp)⟩

variable [IsDomain Λ]

instance isPrincipalIdealRing_bot : IsPrincipalIdealRing (⊥ : Subring Λ) :=
  IsPrincipalIdealRing.of_surjective _ intCast_surjective_bot

instance isRegularRing_bot : IsRegularRing (⊥ : Subring Λ) := inferInstance

instance isTorsionFree_bot : Module.IsTorsionFree (⊥ : Subring Λ) Λ := by
  have : IsDomain (⊥ : Subring Λ) := inferInstance
  have : FaithfulSMul (⊥ : Subring Λ) Λ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  exact FaithfulSMul.to_isTorsionFree _ _

instance flat_bot : Module.Flat (⊥ : Subring Λ) Λ := by
  have : IsDedekindDomain (⊥ : Subring Λ) := inferInstance
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- If `Λ` is a discrete valuation ring in which every prime number is zero, a unit, or a
uniformizer, then `Λ` is a regular algebra over its smallest subring. -/
theorem regularAlgebra_bot [IsDiscreteValuationRing Λ]
    (hΛ : ∀ n : ℤ, Prime n →
      (n : Λ) = 0 ∨ IsUnit (n : Λ) ∨ Ideal.span {(n : Λ)} = maximalIdeal Λ) :
    RegularAlgebra (⊥ : Subring Λ) Λ :=
  regularAlgebra_of_isLocalRing intCast_surjective_bot
    (map_prime_eq_of_intCast intCast_surjective_bot hΛ)

/-- Let `Λ` be a local domain whose residue field has characteristic `p`, where `p` is zero in
`Λ` or generates the maximal ideal. Then every prime number is zero, a unit, or a generator of
the maximal ideal of `Λ`. -/
theorem intCast_prime_cases [IsLocalRing Λ] (p : ℕ) [CharP (ResidueField Λ) p]
    (hp : (p : Λ) = 0 ∨ Ideal.span {(p : Λ)} = maximalIdeal Λ) (n : ℤ) (hn : Prime n) :
    (n : Λ) = 0 ∨ IsUnit (n : Λ) ∨ Ideal.span {(n : Λ)} = maximalIdeal Λ := by
  by_cases hres : residue Λ (n : Λ) = 0
  · have hdvd : (p : ℤ) ∣ n := by
      rw [map_intCast, CharP.intCast_eq_zero_iff (ResidueField Λ) p] at hres
      exact hres
    have hpp : Nat.Prime p := by
      rcases CharP.char_is_prime_or_zero (ResidueField Λ) p with h | rfl
      · exact h
      · exact (hn.ne_zero (zero_dvd_iff.mp (by exact_mod_cast hdvd))).elim
    have hassoc : Associated (p : Λ) (n : Λ) := by
      have := (Nat.prime_iff_prime_int.mp hpp).associated_of_dvd hn hdvd
      simpa using this.map (Int.castRingHom Λ)
    rcases hp with hp | hp
    · left
      exact (hassoc.eq_zero_iff).mp hp
    · right; right
      rw [← hp]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm
  · right; left
    rwa [residue_eq_zero_iff, notMem_maximalIdeal] at hres

/-- `chartConclusion_of_presentation` over the smallest subring of a discrete valuation ring
`Λ`, whose prime numbers are zero, units or uniformizers. -/
theorem chartConclusion_of_dvr
    {W' : Type u} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
    [IsAdicComplete (maximalIdeal W') W'] {ϖ : W'} (hϖ : Irreducible ϖ)
    [IsDiscreteValuationRing Λ]
    (hΛ : ∀ n : ℤ, Prime n →
      (n : Λ) = 0 ∨ IsUnit (n : Λ) ∨ Ideal.span {(n : Λ)} = maximalIdeal Λ)
    (ψ : Λ →+* W') [IsLocalHom ψ]
    (F : Λ[X]) (hFm : F.Monic) (hFϖ : eval₂ ψ ϖ F = 0) (hF0 : F.coeff 0 ∉ maximalIdeal Λ ^ 2)
    (hsurj : ∀ y : W', ∃ q : Λ[X], eval₂ ψ ϖ q = y)
    (hdvd : ∀ q : Λ[X], eval₂ ψ ϖ q = 0 → F ∣ q)
    (C : Type w) [CommRing C] [Algebra.FiniteType ℤ C] (F' : C →+* FractionRing W') :
    ChartConclusion W' C F' :=
  chartConclusion_of_presentation hϖ intCast_surjective_bot (regularAlgebra_bot hΛ) ψ F hFm hFϖ
    hF0 hsurj hdvd C F'

end Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation
