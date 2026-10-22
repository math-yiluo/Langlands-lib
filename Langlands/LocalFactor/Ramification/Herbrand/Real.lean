import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real polygon underlying the Herbrand function

A finite sum of clamped linear functions gives the polygon for a sequence
of positive group orders which is eventually one. Its inverse is constructed
from proved strict monotonicity and surjectivity.
-/

noncomputable section

namespace Langlands.Ramification.Herbrand

open scoped BigOperators

/-- The unit ramp starting at the nonnegative integer `i`. -/
def ramp (i : ℕ) (u : ℝ) : ℝ := min 1 (max 0 (u - i))

theorem ramp_nonneg (i : ℕ) (u : ℝ) : 0 ≤ ramp i u :=
  le_min zero_le_one (le_max_left _ _)

theorem ramp_monotone (i : ℕ) : Monotone (ramp i) := by
  intro u v huv
  exact min_le_min_left _ (max_le_max_left _ (sub_le_sub_right huv _))

theorem ramp_continuous (i : ℕ) : Continuous (ramp i) :=
  continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))

theorem ramp_eq_zero {i : ℕ} {u : ℝ} (hu : u ≤ i) : ramp i u = 0 := by
  simp [ramp, max_eq_left (sub_nonpos.mpr hu)]

theorem ramp_eq_one {i : ℕ} {u : ℝ} (hu : (i : ℝ) + 1 ≤ u) :
    ramp i u = 1 := by
  have h : 1 ≤ u - i := by linarith
  exact min_eq_left (h.trans (le_max_right _ _))

theorem ramp_eq_sub {i : ℕ} {u : ℝ} (hlo : (i : ℝ) ≤ u)
    (hhi : u ≤ (i : ℝ) + 1) : ramp i u = u - i := by
  simp [ramp, max_eq_right (sub_nonneg.mpr hlo), min_eq_right (by linarith : u - i ≤ 1)]

/-- The real polygon determined by the orders `g i`, with cutoff `b`.
The later ramification specialization proves that its orders equal one
past this cutoff. Below zero the polygon is extended by the identity. -/
def polygon (g : ℕ → ℕ) (b : ℕ) (u : ℝ) : ℝ :=
  min u 0 + (max u 0 +
    ∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u) / g 0

theorem polygon_continuous (g : ℕ → ℕ) (b : ℕ) :
    Continuous (polygon g b) := by
  unfold polygon ramp
  fun_prop

theorem polygon_of_nonpos (g : ℕ → ℕ) (b : ℕ) {u : ℝ} (hu : u ≤ 0) :
    polygon g b u = u := by
  have hr (i : ℕ) : ramp i u = 0 :=
    ramp_eq_zero (hu.trans (Nat.cast_nonneg i))
  simp [polygon, min_eq_left hu, max_eq_right hu, hr]

@[simp] theorem polygon_zero (g : ℕ → ℕ) (b : ℕ) : polygon g b 0 = 0 :=
  polygon_of_nonpos g b le_rfl

theorem polygon_of_nonneg (g : ℕ → ℕ) (b : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    polygon g b u =
      (u + ∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u) / g 0 := by
  simp [polygon, min_eq_right hu, max_eq_left hu]

variable {g : ℕ → ℕ} {b : ℕ}

theorem polygon_sum_nonneg (hg : ∀ i, 1 ≤ g i) (u : ℝ) :
    0 ≤ ∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (ramp_nonneg i u)
  exact sub_nonneg.mpr (by exact_mod_cast hg (i + 1))

theorem polygon_lower_bound (hg : ∀ i, 1 ≤ g i) {u : ℝ} (hu : 0 ≤ u) :
    u / (g 0 : ℝ) ≤ polygon g b u := by
  rw [polygon_of_nonneg g b hu]
  exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (polygon_sum_nonneg hg u))
    (Nat.cast_nonneg _)

theorem polygon_strictMono (hg : ∀ i, 1 ≤ g i) : StrictMono (polygon g b) := by
  have hg0 : 0 < (g 0 : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hg 0)
  have hsum : Monotone (fun u : ℝ =>
      ∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u) := by
    intro u v huv
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (ramp_monotone i huv)
      (sub_nonneg.mpr (by exact_mod_cast hg (i + 1)))
  intro u v huv
  by_cases hv : v ≤ 0
  · rw [polygon_of_nonpos g b hv, polygon_of_nonpos g b (huv.le.trans hv)]
    exact huv
  by_cases hu : 0 ≤ u
  · rw [polygon_of_nonneg g b hu, polygon_of_nonneg g b (hu.trans huv.le)]
    exact div_lt_div_of_pos_right (add_lt_add_of_lt_of_le huv (hsum huv.le)) hg0
  · rw [polygon_of_nonpos g b (le_of_not_ge hu)]
    have hnonneg : 0 ≤ polygon g b v :=
      (div_nonneg (le_of_not_ge hv) hg0.le).trans (polygon_lower_bound hg (le_of_not_ge hv))
    exact (lt_of_not_ge hu).trans_le hnonneg

theorem polygon_surjective (hg : ∀ i, 1 ≤ g i) :
    Function.Surjective (polygon g b) := by
  have hg0 : 0 < (g 0 : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hg 0)
  intro v
  apply mem_range_of_exists_le_of_exists_ge (polygon_continuous g b)
  · refine ⟨min v 0, ?_⟩
    rw [polygon_of_nonpos g b (min_le_right _ _)]
    exact min_le_left _ _
  · refine ⟨max v 0 * (g 0 : ℝ), ?_⟩
    have h := polygon_lower_bound (b := b) hg
      (mul_nonneg (le_max_right v 0) hg0.le)
    rw [mul_div_cancel_right₀ _ hg0.ne'] at h
    exact (le_max_left v 0).trans h

/-- The genuine order isomorphism; no inverse or bijectivity is supplied. -/
def polygonOrderIso (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (polygon g b)
    (polygon_strictMono hg) (polygon_surjective hg)

@[simp] theorem polygonOrderIso_apply (g : ℕ → ℕ) (b : ℕ)
    (hg : ∀ i, 1 ≤ g i) (u : ℝ) : polygonOrderIso g b hg u = polygon g b u := rfl

/-- The inverse function obtained from the proved order isomorphism. -/
def inverse (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i) : ℝ → ℝ :=
  (polygonOrderIso g b hg).symm

@[simp] theorem polygon_inverse (g : ℕ → ℕ) (b : ℕ)
    (hg : ∀ i, 1 ≤ g i) (v : ℝ) :
    polygon g b (inverse g b hg v) = v :=
  (polygonOrderIso g b hg).apply_symm_apply v

@[simp] theorem inverse_polygon (g : ℕ → ℕ) (b : ℕ)
    (hg : ∀ i, 1 ≤ g i) (u : ℝ) :
    inverse g b hg (polygon g b u) = u :=
  (polygonOrderIso g b hg).symm_apply_apply u

theorem inverse_continuous (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i) :
    Continuous (inverse g b hg) := (polygonOrderIso g b hg).symm.continuous

theorem inverse_strictMono (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i) :
    StrictMono (inverse g b hg) := (polygonOrderIso g b hg).symm.strictMono

theorem inverse_of_nonpos (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i)
    {v : ℝ} (hv : v ≤ 0) : inverse g b hg v = v := by
  simpa only [polygon_of_nonpos g b hv] using inverse_polygon g b hg v

private theorem sum_range_eq_of_vanishing (f : ℕ → ℝ) (a b : ℕ)
    (ha : ∀ i, a ≤ i → f i = 0) (hb : ∀ i, b ≤ i → f i = 0) :
    ∑ i ∈ Finset.range a, f i = ∑ i ∈ Finset.range b, f i := by
  rcases le_total a b with hab | hba
  · apply Finset.sum_subset (Finset.range_mono hab)
    intro i _ hi
    exact ha i (le_of_not_gt (by simpa using hi))
  · symm
    apply Finset.sum_subset (Finset.range_mono hba)
    intro i _ hi
    exact hb i (le_of_not_gt (by simpa using hi))

/-- Exact affine formula on every closed unit interval, including both
endpoints. The cutoff disappears when the orders are one beyond it. -/
theorem polygon_on_unit_interval (g : ℕ → ℕ) (b : ℕ)
    (htail : ∀ i, b ≤ i → g (i + 1) = 1)
    (n : ℕ) {u : ℝ} (hlo : (n : ℝ) ≤ u) (hhi : u ≤ (n : ℝ) + 1) :
    polygon g b u =
      ((∑ i ∈ Finset.range n, (g (i + 1) : ℝ)) +
        (u - n) * g (n + 1)) / g 0 := by
  rw [polygon_of_nonneg g b ((Nat.cast_nonneg n).trans hlo)]
  have hsum :
      (∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u) =
        ∑ i ∈ Finset.range (n + 1), ((g (i + 1) : ℝ) - 1) * ramp i u := by
    apply sum_range_eq_of_vanishing
    · intro i hi
      simp [htail i hi]
    · intro i hi
      have hni : (n : ℝ) + 1 ≤ i := by exact_mod_cast hi
      rw [ramp_eq_zero (hhi.trans hni), mul_zero]
  rw [hsum, Finset.sum_range_succ, ramp_eq_sub hlo hhi]
  have hprefix :
      (∑ i ∈ Finset.range n, ((g (i + 1) : ℝ) - 1) * ramp i u) =
        (∑ i ∈ Finset.range n, (g (i + 1) : ℝ)) - n := by
    calc
      _ = ∑ i ∈ Finset.range n, ((g (i + 1) : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i + 1 ≤ n := Finset.mem_range.mp hi
        have hireal : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
        rw [ramp_eq_one (hireal.trans hlo), mul_one]
      _ = _ := by simp [Finset.sum_sub_distrib]
  rw [hprefix]
  congr 1
  ring

/-- Serre's formula with `n = floor u`, expressed with natural indexing
for the nonnegative half-line. -/
theorem polygon_floor (g : ℕ → ℕ) (b : ℕ)
    (htail : ∀ i, b ≤ i → g (i + 1) = 1) {u : ℝ} (hu : 0 ≤ u) :
    polygon g b u =
      ((∑ i ∈ Finset.range ⌊u⌋₊, (g (i + 1) : ℝ)) +
        (u - ⌊u⌋₊) * g (⌊u⌋₊ + 1)) / g 0 :=
  polygon_on_unit_interval g b htail ⌊u⌋₊ (Nat.floor_le hu)
    (Nat.lt_floor_add_one u).le

/-- Restriction of the proved real order isomorphism to Serre's half-line. -/
def halfLineOrderIso (g : ℕ → ℕ) (b : ℕ) (hg : ∀ i, 1 ≤ g i) :
    Set.Ici (-1 : ℝ) ≃o Set.Ici (-1 : ℝ) :=
  ((polygonOrderIso g b hg).Ici (-1)).trans
    (Set.orderIsoOfEq _ _ (by
      rw [polygonOrderIso_apply, polygon_of_nonpos g b (by norm_num : (-1 : ℝ) ≤ 0)]))

end Langlands.Ramification.Herbrand
