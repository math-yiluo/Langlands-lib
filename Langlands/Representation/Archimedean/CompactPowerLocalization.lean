import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Recovering a sign by concentrating powers on a maximum level -/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Archimedean

universe u

/-- Nonnegative integrals against all powers of a continuous weight in `[0, 1]`
force a continuous function to be nonnegative on the weight's level one,
provided the function is constant there. -/
def CompactPowerLocalizationStatement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] [IsOpenPosMeasure μ]
    {p f : X → ℝ} {x₀ : X},
    Continuous p → Continuous f → (∀ x, p x ∈ Icc 0 1) →
    p x₀ = 1 → (∀ x, p x = 1 → f x = f x₀) →
    (∀ m : ℕ, 0 ≤ ∫ x, p x ^ m * f x ∂μ) → 0 ≤ f x₀

theorem compactPowerLocalization : CompactPowerLocalizationStatement.{u} := by
  intro X _ _ _ _ _ μ _ _ p f x₀ hp hf hpRange hpAt hlevel hIntegral
  by_contra! hneg
  let ε := -(f x₀) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let nonnegative := {x | 0 ≤ f x}
  have hcompact : IsCompact nonnegative :=
    (isClosed_le continuous_const hf).isCompact
  obtain ⟨r, hr₀, hr₁, hr⟩ :
      ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ x ∈ nonnegative, p x ≤ r := by
    rcases eq_empty_or_nonempty nonnegative with hempty | hnonempty
    · exact ⟨0, le_rfl, zero_lt_one, by simp [hempty]⟩
    obtain ⟨y, hy, hyMax⟩ := hcompact.exists_isMaxOn hnonempty hp.continuousOn
    refine ⟨p y, (hpRange y).1, lt_of_le_of_ne (hpRange y).2 ?_, hyMax⟩
    intro he
    exact (not_le_of_gt hneg) (hlevel y he ▸ hy)
  obtain ⟨s, hrs, hs₁⟩ := exists_between hr₁
  have hs₀ : 0 < s := hr₀.trans_lt hrs
  let U := {x | s < p x} ∩ {x | f x < -ε}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hp).inter (isOpen_lt hf continuous_const)
  have hxU : x₀ ∈ U := ⟨by simpa [hpAt] using hs₁, by dsimp [ε]; linarith⟩
  have hmass : 0 < μ.real U :=
    ENNReal.toReal_pos (hU.measure_pos μ ⟨x₀, hxU⟩).ne' (measure_ne_top μ U)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hbound (x : X) : f x ≤ M :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM x (mem_univ x))
  have hM₀ : 0 ≤ M := (norm_nonneg (f x₀)).trans (hM x₀ (mem_univ x₀))
  have hestimate (m : ℕ) :
      (∫ x, (p x / s) ^ m * f x ∂μ) ≤
        μ.real univ * (M * (r / s) ^ m) + μ.real U * (-ε) := by
    let C := M * (r / s) ^ m
    have hC : 0 ≤ C := mul_nonneg hM₀ (pow_nonneg (div_nonneg hr₀ hs₀.le) _)
    have hleft : Integrable (fun x => (p x / s) ^ m * f x) μ :=
      (((hp.div_const s).pow m).mul hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hright : Integrable (U.indicator (fun _ => -ε)) μ :=
      (integrable_const _).indicator hU.measurableSet
    have hmono := integral_mono hleft ((integrable_const C).add hright) (fun x => by
      have hpower : 0 ≤ (p x / s) ^ m :=
        pow_nonneg (div_nonneg (hpRange x).1 hs₀.le) _
      change (p x / s) ^ m * f x ≤ C + U.indicator (fun _ => -ε) x
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        have hlarge : 1 ≤ (p x / s) ^ m :=
          one_le_pow₀ ((le_div_iff₀ hs₀).2 (by simpa using hx.1.le))
        calc
          (p x / s) ^ m * f x ≤ (p x / s) ^ m * (-ε) :=
            mul_le_mul_of_nonneg_left hx.2.le hpower
          _ ≤ 1 * (-ε) := mul_le_mul_of_nonpos_right hlarge (neg_nonpos.mpr hε.le)
          _ ≤ C + (-ε) := by linarith
      · rw [indicator_of_notMem hx, add_zero]
        by_cases hfx : 0 ≤ f x
        · exact mul_le_mul
            (pow_le_pow_left₀ (div_nonneg (hpRange x).1 hs₀.le)
              (div_le_div_of_nonneg_right (hr x hfx) hs₀.le) _)
            (hbound x) hfx (pow_nonneg (div_nonneg hr₀ hs₀.le) _) |>.trans_eq (mul_comm _ _)
        · exact (mul_nonpos_of_nonneg_of_nonpos hpower (le_of_not_ge hfx)).trans hC)
    rwa [integral_add' (integrable_const C) hright, integral_const,
      integral_indicator_const _ hU.measurableSet, smul_eq_mul, smul_eq_mul] at hmono
  have hlim : Tendsto (fun m : ℕ => μ.real univ * (M * (r / s) ^ m)) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr₀ hs₀.le)
      ((div_lt_one hs₀).2 hrs)
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hpow)
  obtain ⟨m, hm⟩ := ((tendsto_order.1 hlim).2 _ (mul_pos hmass hε)).exists
  have hnormalized : 0 ≤ ∫ x, (p x / s) ^ m * f x ∂μ := by
    simp_rw [div_pow, div_eq_mul_inv]
    have heq : (fun x => p x ^ m * (s ^ m)⁻¹ * f x) =
        fun x => (s ^ m)⁻¹ * (p x ^ m * f x) := by
      funext x
      ring
    rw [heq, integral_const_mul]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hs₀.le _)) (hIntegral m)
  linarith [hestimate m]

end Langlands.Archimedean
