import Langlands.Representation.Archimedean.RealInducedSwapBalanced
import Langlands.Representation.Archimedean.RealInducedSwapIntegralReduction

/-!
# Integral choices for balanced induction-block crossings

The four integer parameters determine denominator choices and positive-root
cancellation cutoffs. Opposite intervals give balanced raw or divided families.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapIntegralNormalization

open Langlands.LocalFactor.Archimedean
open RealCharacterInducedSwap RealCharacterPair
open RealInducedSwapRegularizedFamily RealInducedSwapRegularization
open RealInducedSwapBalanced RealInducedSwapIntegralReduction

/-- Select the unique possible denominator root, if one occurs. -/
def integerChoice (t ε : ℤ) : Option ℕ := by
  classical
  exact if h : ∃ r : ℕ, t = -(ε + 2 * (r : ℤ) + 1) then some h.choose else none

theorem integerChoice_valid (t ε : ℤ) :
    ValidChoice (t : ℂ) ε (integerChoice t ε) := by
  classical
  unfold integerChoice
  split_ifs with h
  · have hr := h.choose_spec
    change (t : ℂ) = -((ε : ℂ) + 2 * (h.choose : ℂ) + 1)
    exact_mod_cast hr
  · intro r hr
    apply h
    exact ⟨r, by exact_mod_cast hr⟩

theorem negative_root_iff {t ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    (∃ r : ℕ, t = -(ε + 2 * (r : ℤ) + 1)) ↔
      t < 0 ∧ (t + ε) % 2 = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    omega
  · rintro ⟨ht, hp⟩
    refine ⟨((-t - ε - 1) / 2).toNat, ?_⟩
    omega

theorem integerChoice_order {t ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    order (integerChoice t ε) = if t < 0 ∧ (t + ε) % 2 = 1 then 1 else 0 := by
  classical
  by_cases h : ∃ r : ℕ, t = -(ε + 2 * (r : ℤ) + 1)
  · simp only [integerChoice, dite_eq_left h, order,
      ite_eq_left ((negative_root_iff hε).mp h)]
  · simp only [integerChoice, dite_eq_right h, order,
      ite_eq_right (fun hn => h ((negative_root_iff hε).mpr hn))]

theorem integerChoice_eq_none_of_positive {t ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (ht : 0 < t) : integerChoice t ε = none := by
  have hn : ¬ ∃ r : ℕ, t = -(ε + 2 * (r : ℤ) + 1) := by
    rintro ⟨r, hr⟩
    omega
  simp only [integerChoice, dite_eq_right hn]

/-- A positive root cuts the parity-restricted multiplier off at that integer. -/
theorem integerChoice_finite {t ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (ht : 0 < t) (hp : (t + ε) % 2 = 1) :
    RealInducedSwapCancellation.FiniteModes t.toNat
      (multiplier (t : ℂ) ε (integerChoice t ε) 0) := by
  have hr : ∃ r : ℕ, t = ε + 2 * (r : ℤ) + 1 := by
    refine ⟨((t - ε - 1) / 2).toNat, ?_⟩
    omega
  obtain ⟨r, hr⟩ := hr
  have hc : (t : ℂ) = (ε : ℂ) + 2 * (r : ℂ) + 1 := by exact_mod_cast hr
  have hcut : ε.toNat + 2 * r + 1 = t.toNat := by omega
  rw [integerChoice_eq_none_of_positive hε ht, ← hcut]
  exact multiplier_finite_at_positive hε r hc

/-- Integer choices for the four parameters in an induction crossing. -/
def intervalChoices (p q m : ℕ) : Choices where
  bc := integerChoice (-(m : ℤ)) (((q + 1) % 2 : ℕ) : ℤ)
  ac := integerChoice ((p : ℤ) - m) (((p + q) % 2 : ℕ) : ℤ)
  bd := integerChoice ((q : ℤ) - m) 0
  ad := integerChoice ((p : ℤ) + q - m) (((p + 1) % 2 : ℕ) : ℤ)

/-- Divide exactly when a positive root gives a supported cancellation. -/
def intervalNormalization (p q m : ℕ) : Normalization where
  choices := intervalChoices p q m
  divide := decide (m < p ∨ m < q ∨ m % 2 = q % 2)

theorem parity_bc (d e : ComplexCharacterData) :
    pairParity (chA e) (chB d) = (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) := by
  change (((((e.weight.natAbs + 1) % 2) + 0) % 2 : ℕ) : ℤ) = _
  congr 1
  omega

theorem parity_ac (d e : ComplexCharacterData) :
    pairParity (chA e) (chA d) =
      (((d.weight.natAbs + e.weight.natAbs) % 2 : ℕ) : ℤ) := by
  change (((((e.weight.natAbs + 1) % 2) +
    ((d.weight.natAbs + 1) % 2)) % 2 : ℕ) : ℤ) = _
  congr 1
  omega

theorem parity_bd (d e : ComplexCharacterData) :
    pairParity (chB e) (chB d) = 0 := rfl

theorem parity_ad (d e : ComplexCharacterData) :
    pairParity (chB e) (chA d) = (((d.weight.natAbs + 1) % 2 : ℕ) : ℤ) := by
  change (((0 + ((d.weight.natAbs + 1) % 2)) % 2 : ℕ) : ℤ) = _
  congr 1
  omega

/-- The remaining three parameters are integral translates of the first. -/
theorem exponent_differences {d e : ComplexCharacterData} {m : ℕ}
    (hm : (chB d).exponent - (chA e).exponent = -(m : ℂ)) :
    (chA d).exponent - (chA e).exponent = ((d.weight.natAbs : ℤ) - m : ℤ) ∧
    (chB d).exponent - (chB e).exponent = ((e.weight.natAbs : ℤ) - m : ℤ) ∧
    (chA d).exponent - (chB e).exponent =
      ((d.weight.natAbs : ℤ) + e.weight.natAbs - m : ℤ) := by
  simp only [chA_exponent, chB_exponent] at *
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  constructor
  · linear_combination hm
  constructor <;> linear_combination hm

/-- The choices agree with the four actual character parameters. -/
theorem intervalChoices_valid {d e : ComplexCharacterData} {m : ℕ}
    (hm : (chB d).exponent - (chA e).exponent = -(m : ℂ)) :
    Valid d e (intervalChoices d.weight.natAbs e.weight.natAbs m) := by
  obtain ⟨hac, hbd, had⟩ := exponent_differences hm
  unfold Valid intervalChoices
  rw [hm, hac, hbd, had, parity_bc, parity_ac, parity_bd, parity_ad]
  exact ⟨by simpa only [Int.cast_neg, Int.cast_natCast] using
    integerChoice_valid (-(m : ℤ)) (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ),
    integerChoice_valid _ _, integerChoice_valid _ _, integerChoice_valid _ _⟩

/-- Root indicators reduce the total order to three parity tests. -/
theorem intervalChoices_totalOrder {p q m : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hmin : min p q ≤ m) (hmax : m ≤ max p q) :
    totalOrder (intervalChoices p q m) =
      (if q < m ∧ m % 2 ≠ q % 2 then 1 else 0) +
      (if p < m ∧ m % 2 ≠ q % 2 then 1 else 0) +
      (if m % 2 = q % 2 then 1 else 0) := by
  have hbc : ((-(m : ℤ) < 0 ∧ (-(m : ℤ) + ((q + 1) % 2 : ℕ)) % 2 = 1) ↔
      m % 2 = q % 2) := by omega
  have hac : ((((p : ℤ) - m < 0 ∧
      ((p : ℤ) - m + ((p + q) % 2 : ℕ)) % 2 = 1)) ↔
      p < m ∧ m % 2 ≠ q % 2) := by omega
  have hbd : ((((q : ℤ) - m < 0 ∧ ((q : ℤ) - m + 0) % 2 = 1)) ↔
      q < m ∧ m % 2 ≠ q % 2) := by omega
  have had : ¬ ((p : ℤ) + q - m < 0 ∧
      ((p : ℤ) + q - m + ((p + 1) % 2 : ℕ)) % 2 = 1) := by omega
  simp only [totalOrder, intervalChoices, integerChoice_order (by omega :
    ((((p + 1) % 2 : ℕ) : ℤ) = 0 ∨ (((p + 1) % 2 : ℕ) : ℤ) = 1)),
    integerChoice_order (by omega : (0 : ℤ) = 0 ∨ (0 : ℤ) = 1),
    integerChoice_order (by omega :
      ((((p + q) % 2 : ℕ) : ℤ) = 0 ∨ (((p + q) % 2 : ℕ) : ℤ) = 1)),
    integerChoice_order (by omega :
      ((((q + 1) % 2 : ℕ) : ℤ) = 0 ∨ (((q + 1) % 2 : ℕ) : ℤ) = 1)),
    hbc, hac, hbd, had, ite_false, zero_add]

/-- The reversed interval stays between the same two endpoints. -/
theorem reverse_interval {p q m : ℕ} (hmin : min p q ≤ m) (hmax : m ≤ max p q) :
    min q p ≤ p + q - m ∧ p + q - m ≤ max q p := by omega

/-- At most one negative root is present in the interval. -/
theorem intervalChoices_totalOrder_indicator {p q m : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hmin : min p q ≤ m) (hmax : m ≤ max p q) :
    totalOrder (intervalChoices p q m) =
      if p < m ∨ q < m ∨ m % 2 = q % 2 then 1 else 0 := by
  rw [intervalChoices_totalOrder hp hq hmin hmax]
  have hn : ¬ (p < m ∧ q < m) := by omega
  split_ifs <;> omega

/-- Opposite choices remove exactly the total number of selected divisions. -/
theorem intervalNormalization_balanced {p q m : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hmin : min p q ≤ m) (hmax : m ≤ max p q) :
    RealInducedSwapBalanced.Balanced (intervalNormalization p q m)
      (intervalNormalization q p (p + q - m)) := by
  have hr := reverse_interval hmin hmax
  have hsum : p + q - m + m = p + q := by omega
  have hpar : (p + q - m) % 2 = p % 2 ↔ m % 2 = q % 2 := by omega
  have hp' : p < p + q - m ↔ m < q := by omega
  have hq' : q < p + q - m ↔ m < p := by omega
  have hp'' : p + q - m < p ↔ q < m := by omega
  have hq'' : p + q - m < q ↔ p < m := by omega
  unfold RealInducedSwapBalanced.Balanced intervalNormalization divisionOrder
  rw [intervalChoices_totalOrder_indicator hp hq hmin hmax,
    intervalChoices_totalOrder_indicator hq hp hr.1 hr.2]
  simp only [decide_eq_true_eq, hpar, hp', hq', hp'', hq'']
  exact Nat.add_comm _ _

/-- Every selected division is justified by a positive middle or final root. -/
theorem intervalChoices_cancels {d e : ComplexCharacterData} {m : ℕ}
    (hp : 0 < d.weight.natAbs) (hq : 0 < e.weight.natAbs)
    (hmin : min d.weight.natAbs e.weight.natAbs ≤ m)
    (hmax : m ≤ max d.weight.natAbs e.weight.natAbs)
    (hm : (chB d).exponent - (chA e).exponent = -(m : ℂ))
    (hdiv : m < d.weight.natAbs ∨ m < e.weight.natAbs ∨
      m % 2 = e.weight.natAbs % 2) :
    Cancels d e (intervalChoices d.weight.natAbs e.weight.natAbs m) := by
  obtain ⟨hac, hbd, had⟩ := exponent_differences hm
  unfold Cancels
  rw [hac, hbd, had, parity_ac, parity_bd, parity_ad]
  by_cases hpar : m % 2 = e.weight.natAbs % 2
  · right; right
    refine ⟨((d.weight.natAbs : ℤ) + e.weight.natAbs - m).toNat, by omega, ?_⟩
    exact integerChoice_finite (by omega) (by omega) (by omega)
  · rcases hdiv with hlt | hlt | heq
    · left
      refine ⟨((d.weight.natAbs : ℤ) - m).toNat, by omega, ?_⟩
      exact integerChoice_finite (by omega) (by omega) (by omega)
    · right; left
      refine ⟨((e.weight.natAbs : ℤ) - m).toNat, by omega, ?_⟩
      exact integerChoice_finite (by omega) (by omega) (by omega)
    · exact (hpar heq).elim

/-- The interval normalizations are valid on the actual character parameters. -/
theorem intervalNormalization_valid {d e : ComplexCharacterData} {m : ℕ}
    (hp : 0 < d.weight.natAbs) (hq : 0 < e.weight.natAbs)
    (hmin : min d.weight.natAbs e.weight.natAbs ≤ m)
    (hmax : m ≤ max d.weight.natAbs e.weight.natAbs)
    (hm : (chB d).exponent - (chA e).exponent = -(m : ℂ)) :
    IsValid d e (intervalNormalization d.weight.natAbs e.weight.natAbs m) := by
  refine ⟨intervalChoices_valid hm, ?_⟩
  intro hdiv
  apply intervalChoices_cancels hp hq hmin hmax hm
  exact of_decide_eq_true hdiv

/-- The reverse first parameter is the negative complementary integer. -/
theorem reverse_parameter {d e : ComplexCharacterData} {m : ℕ}
    (hmax : m ≤ max d.weight.natAbs e.weight.natAbs)
    (hm : (chB d).exponent - (chA e).exponent = -(m : ℂ)) :
    (chB e).exponent - (chA d).exponent =
      -((d.weight.natAbs + e.weight.natAbs - m : ℕ) : ℂ) := by
  have hsum : m ≤ d.weight.natAbs + e.weight.natAbs := by omega
  rw [Nat.cast_sub hsum, Nat.cast_add]
  simp only [chA_exponent, chB_exponent] at *
  linear_combination -hm

/-- Balanced choices exist throughout the integral window of the swap reduction. -/
theorem exists_balanced_of_integralWindow {d e : ComplexCharacterData}
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (_hweights : d.weight.natAbs ≠ e.weight.natAbs) (m : ℕ)
    (hw : IntegralWindow d e m) :
    ∃ a b : Normalization, IsValid d e a ∧ IsValid e d b ∧
      RealInducedSwapBalanced.Balanced a b := by
  have hp : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hd
  have hq : 0 < e.weight.natAbs := Int.natAbs_pos.mpr he
  have hmax : m ≤ max d.weight.natAbs e.weight.natAbs := by
    have htwice := hw.2.1
    omega
  have hr := reverse_interval hw.1 hmax
  refine ⟨intervalNormalization d.weight.natAbs e.weight.natAbs m,
    intervalNormalization e.weight.natAbs d.weight.natAbs
      (d.weight.natAbs + e.weight.natAbs - m),
    intervalNormalization_valid hp hq hw.1 hmax hw.2.2,
    intervalNormalization_valid hq hp hr.1 hr.2 (reverse_parameter hmax hw.2.2),
    intervalNormalization_balanced hp hq hw.1 hmax⟩

end RealInducedSwapIntegralNormalization
end Langlands.Archimedean
