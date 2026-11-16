import Langlands.Representation.Archimedean.RealInducedSwapGeneric
import Langlands.Representation.Archimedean.RealInducedSwapArithmetic
import Langlands.Representation.Archimedean.RealCharacterInducedUnlinked

/-!
# Reduction of the induced-block swap to unequal integral parameters

The generic construction and equal-parameter identity leave a bounded integral
window. This module identifies that window and proves an exact reduction to it.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean
namespace RealInducedSwapIntegralReduction

open Langlands.LocalFactor.Archimedean
open RealCharacterInducedSwap RealCharacterPair RealBlockMultiplier
open RealInducedSwapGeneric RealInducedSwapArithmetic

/-- The integral window left by the ordered unlinkedness condition. -/
def IntegralWindow (d e : ComplexCharacterData) (m : ℕ) : Prop :=
  min d.weight.natAbs e.weight.natAbs ≤ m ∧
    2 * m ≤ d.weight.natAbs + e.weight.natAbs ∧
    (chB d).exponent - (chA e).exponent = -(m : ℂ)

/-- The remaining local swap for unequal absolute weights in the integral window. -/
def IntegralSwapStatement : Prop :=
  ∀ (d e : ComplexCharacterData),
    d.weight ≠ 0 → e.weight ≠ 0 → d.weight.natAbs ≠ e.weight.natAbs →
      ∀ m : ℕ, IntegralWindow d e m →
        RealInjectiveIntertwinerExists 4 (source d e) (target d e)

theorem natAbs_sub_add_min (p q : ℕ) :
    ((p : ℤ) - q).natAbs + 2 * min p q = p + q := by
  rcases le_total p q with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h, min_eq_left h]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h, min_eq_right h]
    omega

theorem half_sum_eq (p q : ℕ) :
    (((((p : ℤ) - q).natAbs : ℕ) : ℂ) / 2 + ((min p q : ℕ) : ℂ)) =
      (p : ℂ) / 2 + (q : ℂ) / 2 := by
  have h : (((p : ℤ) - q).natAbs : ℂ) + 2 * ((min p q : ℕ) : ℂ) =
      (p : ℂ) + (q : ℂ) := by
    exact_mod_cast natAbs_sub_add_min p q
  linear_combination h / 2

/-- All four constituent parameters are nonintegral if the first one is. -/
theorem generic_of_not_integer (d e : ComplexCharacterData)
    (h : ¬ ∃ z : ℤ, (chB d).exponent - (chA e).exponent = (z : ℂ)) :
    IsGenericPair d e := by
  have hshift (k : ℕ) :
      ¬ ∃ z : ℤ, (chB d).exponent - (chA e).exponent + (k : ℂ) = (z : ℂ) := by
    rintro ⟨z, hz⟩
    apply h
    refine ⟨z - (k : ℤ), ?_⟩
    push_cast
    linear_combination hz
  refine ⟨RealCharacterInducedUnlinked.generic_of_not_integer h, ?_, ?_, ?_⟩
  · apply RealCharacterInducedUnlinked.generic_of_not_integer
    intro hz
    apply hshift d.weight.natAbs
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    simp only [chA_exponent, chB_exponent] at *
    linear_combination hz
  · apply RealCharacterInducedUnlinked.generic_of_not_integer
    intro hz
    apply hshift e.weight.natAbs
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    simp only [chA_exponent, chB_exponent] at *
    linear_combination hz
  · apply RealCharacterInducedUnlinked.generic_of_not_integer
    intro hz
    apply hshift (d.weight.natAbs + e.weight.natAbs)
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    simp only [chA_exponent, chB_exponent] at *
    push_cast
    linear_combination hz

/-- An integral constituent parameter of an ordered unlinked pair lies in the window. -/
theorem integralWindow_of_integer {d e : ComplexCharacterData}
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e))
    (hint : ∃ z : ℤ, (chB d).exponent - (chA e).exponent = (z : ℂ)) :
    ∃ m : ℕ, IntegralWindow d e m := by
  obtain ⟨z, hz⟩ := hint
  have hbound : z + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) ≤ 0 := by
    by_contra hn
    have hpos : 0 < z + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) := by omega
    let k := (z + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ)).toNat
    have hk : 0 < k := by dsimp [k]; omega
    have hki : (k : ℤ) = z + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℤ) := by
      dsimp [k]
      omega
    have hkc : (k : ℂ) = (z : ℂ) + ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) := by
      simpa only [Int.cast_add, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℂ)) hki
    apply (unlinked_iff_of_order hd he horder).mp hun k hk
    rw [hkc]
    have hhalf := half_sum_eq d.weight.natAbs e.weight.natAbs
    rw [chA_exponent, chB_exponent] at hz
    linear_combination hz - hhalf
  let m := (-z).toNat
  have hmi : (m : ℤ) = -z := by dsimp [m]; omega
  have hmc : (m : ℂ) = -(z : ℂ) := by exact_mod_cast hmi
  have hmin : min d.weight.natAbs e.weight.natAbs ≤ m := by omega
  have hw : (chB d).exponent - (chA e).exponent = -(m : ℂ) := by
    rw [hmc, neg_neg]
    exact hz
  have hre := congrArg Complex.re hw
  have hord : e.exponent.re ≤ d.exponent.re := horder
  simp only [chA_exponent, chB_exponent, Complex.sub_re, Complex.add_re,
    Complex.div_ofNat_re, Complex.natCast_re, Complex.neg_re] at hre
  have htwice : (2 : ℝ) * (m : ℝ) ≤
      (d.weight.natAbs : ℝ) + (e.weight.natAbs : ℝ) := by linarith
  exact ⟨m, hmin, by exact_mod_cast htwice, hw⟩

/-- The integral window already implies the original order and unlinkedness conditions. -/
theorem order_unlinked_of_integralWindow {d e : ComplexCharacterData}
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0) {m : ℕ}
    (hw : IntegralWindow d e m) :
    realBlockExponent (.induced e) ≤ realBlockExponent (.induced d) ∧
      AreRealBlocksUnlinked (.induced d) (.induced e) := by
  obtain ⟨hmin, htwice, hparam⟩ := hw
  have hre := congrArg Complex.re hparam
  simp only [chA_exponent, chB_exponent, Complex.sub_re, Complex.add_re,
    Complex.div_ofNat_re, Complex.natCast_re, Complex.neg_re] at hre
  have htwice' : (2 : ℝ) * (m : ℝ) ≤
      (d.weight.natAbs : ℝ) + (e.weight.natAbs : ℝ) := by exact_mod_cast htwice
  have horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d) := by
    change e.exponent.re ≤ d.exponent.re
    linarith
  refine ⟨horder, ?_⟩
  apply (unlinked_iff_of_order hd he horder).mpr
  intro k hk hlinked
  have hhalf := half_sum_eq d.weight.natAbs e.weight.natAbs
  rw [chA_exponent, chB_exponent] at hparam
  have heq : ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) = (m : ℂ) + (k : ℂ) := by
    linear_combination -hparam + hlinked + hhalf
  have heq' : min d.weight.natAbs e.weight.natAbs = m + k := by exact_mod_cast heq
  omega

/-- Equal weights in the integral window give identical visible parameters. -/
theorem exponent_eq_of_equal_weights {d e : ComplexCharacterData} {m : ℕ}
    (hw : IntegralWindow d e m) (hweight : d.weight.natAbs = e.weight.natAbs) :
    d.exponent = e.exponent := by
  obtain ⟨hmin, htwice, hparam⟩ := hw
  have hm : m = d.weight.natAbs := by
    rw [← hweight, min_self] at hmin
    rw [← hweight] at htwice
    omega
  rw [chA_exponent, chB_exponent, hm, ← hweight] at hparam
  linear_combination hparam

/-- A nonintegral first constituent parameter gives the actual swap in every context. -/
theorem injective_of_not_integer {n : ℕ} (pre post : List RealBlock)
    (d e : ComplexCharacterData)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hint : ¬ ∃ z : ℤ, (chB d).exponent - (chA e).exponent = (z : ℂ)) :
    RealInjectiveIntertwinerExists n (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) :=
  injective_in_stages d e pre post hrank (generic_of_not_integer d e hint)

/-- Unequal imaginary exponents give the actual swap in every context. -/
theorem injective_of_im_ne {n : ℕ} (pre post : List RealBlock)
    (d e : ComplexCharacterData)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (him : d.exponent.im ≠ e.exponent.im) :
    RealInjectiveIntertwinerExists n (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  apply injective_of_not_integer pre post d e hrank
  rintro ⟨z, hz⟩
  have h := congrArg Complex.im hz
  simp only [chA_exponent, chB_exponent, Complex.sub_im, Complex.add_im,
    Complex.div_ofNat_im, Complex.natCast_im, Complex.intCast_im, zero_div,
    sub_zero, add_zero] at h
  exact him (sub_eq_zero.mp h)

/-- The ordered unlinked swap is completely proved when the absolute weights agree. -/
theorem injective_of_equal_weights {n : ℕ} (pre post : List RealBlock)
    (d e : ComplexCharacterData) (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.induced e))
    (hweight : d.weight.natAbs = e.weight.natAbs) :
    RealInjectiveIntertwinerExists n (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  by_cases hint : ∃ z : ℤ, (chB d).exponent - (chA e).exponent = (z : ℂ)
  · obtain ⟨m, hw⟩ := integralWindow_of_integer hd he horder hun hint
    exact swap_of_same_parameters n pre post hweight
      (exponent_eq_of_equal_weights hw hweight)
  · exact injective_of_not_integer pre post d e hrank hint

/-- The full target reduces to the unequal-weight integral window, in rank four only. -/
theorem realInducedSwap_iff_integral :
    RealInducedSwapStatement ↔ IntegralSwapStatement := by
  constructor
  · intro h d e hd he _ m hw
    obtain ⟨horder, hun⟩ := order_unlinked_of_integralWindow hd he hw
    exact h 4 [] [] d e hd he rfl horder hun
  · intro h n pre post d e hd he hrank horder hun
    by_cases hint : ∃ z : ℤ, (chB d).exponent - (chA e).exponent = (z : ℂ)
    · obtain ⟨m, hw⟩ := integralWindow_of_integer hd he horder hun hint
      by_cases hweight : d.weight.natAbs = e.weight.natAbs
      · exact swap_of_same_parameters n pre post hweight
          (exponent_eq_of_equal_weights hw hweight)
      · have hlocal := h d e hd he hweight m hw
        simpa only [source, target, RealCharacterPairReducible.mid_pair] using
          hlocal.in_stages pre post rfl rfl
            (by simpa only [source, RealCharacterPairReducible.mid_pair] using hrank)
    · exact injective_in_stages d e pre post hrank (generic_of_not_integer d e hint)

end RealInducedSwapIntegralReduction
end Langlands.Archimedean
