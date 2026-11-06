import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! # An integral boundary direction for a finite weight set -/

namespace Langlands.GroupScheme

/-- Coefficients for a boundary direction that preserves an integral
function's nonnegative region and acquires a new zero on a given set. -/
def IsIntegralBoundaryCombination {ι : Type*} (s : Set ι) (f g : ι → ℤ)
    (n m : ℤ) : Prop :=
  0 < n ∧
    (∀ x ∈ s, 0 ≤ f x → 0 ≤ n * f x + m * g x) ∧
    ∃ x ∈ s, f x ≠ 0 ∧ n * f x + m * g x = 0

/-- If an integral function vanishes wherever another does, but is not
identically zero on a finite set, an integral linear combination reaches
a new zero while preserving the original nonnegative region. -/
theorem exists_integral_boundary_combination {ι : Type*} {s : Set ι}
    (hs : s.Finite) (f g : ι → ℤ)
    (hzero : ∀ x ∈ s, f x = 0 → g x = 0)
    (hgne : ∃ x ∈ s, g x ≠ 0) :
    ∃ n m : ℤ, IsIntegralBoundaryCombination s f g n m := by
  classical
  obtain ⟨a, ha, hga⟩ := hgne
  have hfa : f a ≠ 0 := fun h => hga (hzero a ha h)
  let ratio (x : ι) : ℚ := |(g x : ℚ) / (f x : ℚ)|
  have hra : 0 < ratio a := by
    exact abs_pos.mpr (div_ne_zero (by exact_mod_cast hga) (by exact_mod_cast hfa))
  obtain ⟨b, hb, hmax⟩ := hs.toFinset.exists_max_image ratio
    ⟨a, hs.mem_toFinset.mpr ha⟩
  have hbs : b ∈ s := hs.mem_toFinset.mp hb
  have hrb : 0 < ratio b := hra.trans_le (hmax a (hs.mem_toFinset.mpr ha))
  have hgb : g b ≠ 0 := by
    intro h
    simp [ratio, h] at hrb
  have hfb : f b ≠ 0 := fun h => hgb (hzero b hbs h)
  have hbound (x : ι) (hx : x ∈ s) :
      |g x| * |f b| ≤ |g b| * |f x| := by
    by_cases hfx : f x = 0
    · simp [hfx, hzero x hx hfx]
    · have h := hmax x (hs.mem_toFinset.mpr hx)
      change |(g x : ℚ) / (f x : ℚ)| ≤ |(g b : ℚ) / (f b : ℚ)| at h
      rw [abs_div, abs_div] at h
      have hfx' : (0 : ℚ) < |(f x : ℚ)| :=
        abs_pos.mpr (by exact_mod_cast hfx)
      have hfb' : (0 : ℚ) < |(f b : ℚ)| :=
        abs_pos.mpr (by exact_mod_cast hfb)
      have h' := (div_le_div_iff₀ hfx' hfb').mp h
      exact_mod_cast h'
  rcases lt_or_gt_of_ne hgb with hgbneg | hgbpos
  · refine ⟨-g b, f b, by omega, ?_, b, hbs, hfb, by ring⟩
    intro x hx hfx
    have hbnd := hbound x hx
    rw [abs_of_neg hgbneg, abs_of_nonneg hfx] at hbnd
    have hlo := neg_abs_le (f b * g x)
    rw [abs_mul] at hlo
    nlinarith
  · refine ⟨g b, -f b, hgbpos, ?_, b, hbs, hfb, by ring⟩
    intro x hx hfx
    have hbnd := hbound x hx
    rw [abs_of_pos hgbpos, abs_of_nonneg hfx] at hbnd
    have hup := le_abs_self (f b * g x)
    rw [abs_mul] at hup
    nlinarith

end Langlands.GroupScheme
