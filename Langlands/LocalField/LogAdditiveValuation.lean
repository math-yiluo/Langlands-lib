import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Real additive valuations obtained by normalized negative logarithms -/

noncomputable section

universe u

open scoped NNReal

namespace Langlands.LocalField

/-- Negative logarithm with zero sent to infinity, at a prescribed real scale. -/
def negativeLogValue (c : ℝ) (r : ℝ≥0) : WithTop ℝ :=
  if r = 0 then ⊤ else ((-Real.log (r : ℝ) / c : ℝ) : WithTop ℝ)

@[simp] theorem negativeLogValue_zero (c : ℝ) : negativeLogValue c 0 = ⊤ := by
  simp [negativeLogValue]

@[simp] theorem negativeLogValue_one (c : ℝ) : negativeLogValue c 1 = 0 := by
  simp [negativeLogValue]

theorem negativeLogValue_of_ne_zero (c : ℝ) {r : ℝ≥0} (hr : r ≠ 0) :
    negativeLogValue c r = ((-Real.log (r : ℝ) / c : ℝ) : WithTop ℝ) := by
  simp [negativeLogValue, hr]

theorem negativeLogValue_mul (c : ℝ) (a b : ℝ≥0) :
    negativeLogValue c (a * b) = negativeLogValue c a + negativeLogValue c b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [negativeLogValue, mul_ne_zero ha hb, ha, hb, ite_false, NNReal.coe_mul,
    Real.log_mul (NNReal.coe_ne_zero.mpr ha) (NNReal.coe_ne_zero.mpr hb), neg_add_rev,
    add_div, WithTop.coe_add, add_comm]

theorem negativeLogValue_le_iff {c : ℝ} (hc : 0 < c) (a b : ℝ≥0) :
    negativeLogValue c a ≤ negativeLogValue c b ↔ b ≤ a := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    · simp [negativeLogValue, ha, hb]
  by_cases hb : b = 0
  · simp [negativeLogValue, ha, hb]
  rw [negativeLogValue_of_ne_zero c ha, negativeLogValue_of_ne_zero c hb,
    WithTop.coe_le_coe, div_le_div_iff_of_pos_right hc, neg_le_neg_iff,
    Real.log_le_log_iff (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hb))
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha))]
  exact NNReal.coe_le_coe

/-- A nonnegative-real multiplicative valuation, expressed additively at scale `c`. -/
def logAdditiveValuation {R : Type u} [Ring R] (v : Valuation R ℝ≥0)
    (c : ℝ) (hc : 0 < c) : AddValuation R (WithTop ℝ) :=
  AddValuation.of (fun x => negativeLogValue c (v x))
    (by simp) (by simp)
    (fun x y => by
      rcases le_max_iff.mp (v.map_add x y) with hx | hy
      · exact min_le_of_left_le ((negativeLogValue_le_iff hc _ _).mpr hx)
      · exact min_le_of_right_le ((negativeLogValue_le_iff hc _ _).mpr hy))
    (fun x y => by rw [v.map_mul]; exact negativeLogValue_mul c _ _)

@[simp] theorem logAdditiveValuation_apply {R : Type u} [Ring R]
    (v : Valuation R ℝ≥0) (c : ℝ) (hc : 0 < c) (x : R) :
    logAdditiveValuation v c hc x = negativeLogValue c (v x) := rfl

theorem logAdditiveValuation_le_iff {R : Type u} [Ring R]
    (v : Valuation R ℝ≥0) (c : ℝ) (hc : 0 < c) (x y : R) :
    logAdditiveValuation v c hc x ≤ logAdditiveValuation v c hc y ↔ v y ≤ v x :=
  negativeLogValue_le_iff hc _ _

theorem logAdditiveValuation_of_ne_zero {K : Type u} [Field K]
    (v : Valuation K ℝ≥0) (c : ℝ) (hc : 0 < c) {x : K} (hx : x ≠ 0) :
    logAdditiveValuation v c hc x = ((-Real.log (v x : ℝ) / c : ℝ) : WithTop ℝ) :=
  negativeLogValue_of_ne_zero c (v.ne_zero_iff.mpr hx)

/-- Every map preserving the multiplicative values also preserves the additive values. -/
theorem logAdditiveValuation_invariant {R : Type u} [Ring R]
    (v : Valuation R ℝ≥0) (c : ℝ) (hc : 0 < c) (f : R → R)
    (hf : ∀ x, v (f x) = v x) (x : R) :
    logAdditiveValuation v c hc (f x) = logAdditiveValuation v c hc x := by
  simp only [logAdditiveValuation_apply, hf]

end Langlands.LocalField
