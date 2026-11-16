import Langlands.Representation.Archimedean.RealCharacterInducedGeneric
import Langlands.Representation.Archimedean.RealCharacterInducedEndpoint
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-!
# The unlinked character-induced swap

The exhaustive parameter split combines the generic, interlaced integral and
endpoint constructions, then applies induction in stages.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean
namespace RealCharacterInducedUnlinked

open RealBlockMultiplier RealCharacterPair RealCharacterInducedSwap
open Langlands.LocalFactor.Archimedean

/-- A nonintegral parameter avoids every rank-one exceptional value. -/
theorem generic_of_not_integer {ν : ℂ} {ε : ℤ}
    (h : ¬ ∃ z : ℤ, ν = (z : ℂ)) : IsGenericParameter ν ε := by
  constructor
  · intro m hm
    apply h
    refine ⟨ε + 2 * (m : ℤ) + 1, ?_⟩
    push_cast
    exact hm
  · intro m hm
    apply h
    refine ⟨-(ε + 2 * (m : ℤ) + 1), ?_⟩
    push_cast
    exact hm

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- Nonintegrality of `s-b` makes both factors generic. -/
theorem injective_of_not_integer
    (h : ¬ ∃ z : ℤ, c.exponent - (chB d).exponent = (z : ℂ)) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) := by
  apply RealCharacterInducedGeneric.injective_of_generic c d
  · apply generic_of_not_integer
    rintro ⟨z, hz⟩
    apply h
    refine ⟨z + (d.weight.natAbs : ℤ), ?_⟩
    rw [Int.cast_add, Int.cast_natCast]
    rw [chA_exponent] at hz
    rw [chB_exponent]
    linear_combination hz
  · exact generic_of_not_integer h

/-- At the even endpoint both parameters, `0` and `ell`, are generic. -/
theorem injective_endpoint_even
    (hw : (chB d).exponent - c.exponent = -(d.weight.natAbs : ℂ))
    (hpar : (d.weight.natAbs + c.parity.val) % 2 = 0) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) := by
  have h0 : c.exponent - (chA d).exponent = 0 := by
    rw [chA_exponent, chB_exponent] at *
    linear_combination -hw
  have h1 : c.exponent - (chB d).exponent = (d.weight.natAbs : ℂ) := by
    linear_combination -hw
  apply RealCharacterInducedGeneric.injective_of_generic c d
  · rw [h0]
    have he := pairParity_eq c (chA d)
    have hden : ∀ i : ℕ, (0 : ℂ) ≠ -((pairParity c (chA d) : ℂ) + 2 * i + 1) :=
      ne_neg_of_re_nonneg (by simp) (by omega)
    exact ⟨fun i hi => hden i (by simpa using congrArg Neg.neg hi), hden⟩
  · rw [h1]
    apply isGenericParameter_of_re_nonneg (by simp) (by
      have := pairParity_eq (chB d) c
      omega)
    intro i hi
    have e : (d.weight.natAbs : ℤ) = pairParity (chB d) c + 2 * i + 1 := by
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        Int.cast_one] using hi
    rw [pairParity_chB_c] at e
    have hc := c.parity.isLt
    omega

/-- The GL3 unlinked swap, with the original order and nonzero-weight hypotheses. -/
theorem injective_unlinked (hd : d.weight ≠ 0)
    (hord : realBlockExponent (RealBlock.induced d) ≤ realBlockExponent (RealBlock.character c))
    (hun : AreRealBlocksUnlinked (RealBlock.character c) (RealBlock.induced d)) :
    RealInjectiveIntertwinerExists 3 (lCD c d) (lDC c d) := by
  have hl0 : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hd
  by_cases hint : ∃ z : ℤ, c.exponent - (chB d).exponent = (z : ℂ)
  · obtain ⟨z, hz⟩ := hint
    have hre : c.exponent.re - d.exponent.re + (d.weight.natAbs : ℝ) / 2 = (z : ℝ) := by
      have hr := congrArg Complex.re hz
      have hdiv : (((d.weight.natAbs : ℂ) / 2).re) = (d.weight.natAbs : ℝ) / 2 := by
        simp
      simp only [chB_exponent, Complex.sub_re, Complex.intCast_re, hdiv] at hr
      linarith
    have hord' : d.exponent.re ≤ c.exponent.re := hord
    have hl0' : (0 : ℝ) < d.weight.natAbs := by exact_mod_cast hl0
    have hzpos : 0 < z := by
      have hrz : (0 : ℝ) < z := by linarith
      exact_mod_cast hrz
    let m := z.toNat
    have hm0 : 0 < m := by omega
    have hmz : (m : ℂ) = (z : ℂ) := by
      have hi : (m : ℤ) = z := by omega
      exact_mod_cast hi
    have hw : (chB d).exponent - c.exponent = -(m : ℂ) := by
      rw [hmz]
      linear_combination -hz
    have hlinked : ¬ MoeglinDatum.IsLinked (.character c.parity c.exponent)
        (.discrete d.weight.natAbs d.exponent) :=
      hun _ (by simp [realBlockMoeglinData]) _ (by simp [realBlockMoeglinData, hd])
    have hml : m ≤ d.weight.natAbs := by
      by_contra hnot
      have hmgt : d.weight.natAbs < m := by omega
      apply hlinked
      refine ⟨m - d.weight.natAbs, Nat.sub_pos_of_lt hmgt, Or.inr ?_⟩
      rw [Nat.cast_sub hmgt.le]
      rw [chB_exponent] at hw
      linear_combination -hw
    rcases hml.lt_or_eq with hlt | heq
    · exact RealCharacterInducedInterlaced.injective_interlaced c d hm0 hlt hw
    · rw [heq] at hw
      rcases Nat.mod_two_eq_zero_or_one (d.weight.natAbs + c.parity.val) with hp | hp
      · exact injective_endpoint_even c d hw hp
      · exact RealCharacterInducedEndpoint.injective_endpoint c d hl0 hw hp
  · exact injective_of_not_integer c d hint

end RealCharacterInducedUnlinked

/-- The full character-induced unlinked swap, including arbitrary surrounding blocks. -/
theorem realCharacterInducedSwap : RealCharacterInducedSwapStatement := by
  intro n pre post c d hd hrank hord hun
  have h := RealCharacterInducedUnlinked.injective_unlinked c d hd hord hun
  simpa [RealCharacterInducedSwap.lCD, RealCharacterInducedSwap.lDC] using
    h.in_stages pre post rfl rfl (by simpa using hrank)

end Langlands.Archimedean
