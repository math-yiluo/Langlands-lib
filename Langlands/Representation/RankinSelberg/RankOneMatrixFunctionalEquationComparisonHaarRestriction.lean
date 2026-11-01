import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! A right-invariant ambient bound controls actual subgroup Haar restrictions. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Function
open scoped ENNReal

universe uG uH

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- The fiber which appears when a compact right average is unfolded along
an actual subgroup homomorphism. -/
def haarSubgroupFiber (ι : H →* G) (K : Subgroup G) (x : G) : Set H :=
  {h | (ι h)⁻¹ * x ∈ K}

section Fiber

variable [MeasurableSpace H] [MeasurableMul H]
    (ν : Measure H) [ν.IsMulLeftInvariant]

/-- Every nonempty fiber is a left coset of the inverse image subgroup.
Consequently its Haar measure is bounded by the same fixed subgroup mass. -/
theorem measure_haarSubgroupFiber_le (ι : H →* G) (K : Subgroup G) (x : G) :
    ν (haarSubgroupFiber ι K x) ≤ ν (ι ⁻¹' (K : Set G)) := by
  by_cases he : (haarSubgroupFiber ι K x).Nonempty
  · obtain ⟨h₀, hh₀⟩ := he
    have hset : haarSubgroupFiber ι K x =
        (fun h : H => h₀⁻¹ * h) ⁻¹' (ι ⁻¹' (K : Set G)) := by
      ext h
      change (ι h)⁻¹ * x ∈ K ↔ ι (h₀⁻¹ * h) ∈ K
      have hh₀' : (ι h₀)⁻¹ * x ∈ K := hh₀
      have heq : (ι h)⁻¹ * x = ((ι h₀)⁻¹ * ι h)⁻¹ * ((ι h₀)⁻¹ * x) := by
        group
      rw [heq, K.mul_mem_cancel_right hh₀', K.inv_mem_iff, map_mul, map_inv]
    rw [hset, measure_preimage_mul]
  · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
    exact bot_le

end Fiber

section Restriction

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    [MeasurableSpace H] [MeasurableMul₂ H]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (ν : Measure H) [ν.IsMulLeftInvariant] [SFinite ν]

/-- A nonnegative right-K-invariant function has its actual subgroup Haar
integral bounded by the ambient one, with the two exact subgroup masses.
The subgroup is not required to be open in the ambient group. -/
theorem lintegral_subgroup_le_of_right_invariant
    (ι : H →* G) (hι : Measurable ι) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (F : G → ℝ≥0∞) (hF : Measurable F)
    (hfixed : ∀ k ∈ K, ∀ g, F (g * k) = F g) :
    μ (K : Set G) * (∫⁻ h, F (ι h) ∂ν) ≤
      ν (ι ⁻¹' (K : Set G)) * (∫⁻ x, F x ∂μ) := by
  let χ : G → ℝ≥0∞ := (K : Set G).indicator (fun _ => 1)
  have hχ : Measurable χ := measurable_const.indicator hK
  let Q : H → G → ℝ≥0∞ := fun h x => χ ((ι h)⁻¹ * x) * F x
  have hQ : Measurable (uncurry Q) :=
    (hχ.comp ((hι.comp measurable_fst).inv.mul measurable_snd)).mul
      (hF.comp measurable_snd)
  have hpoint (h : H) : (∫⁻ x, Q h x ∂μ) = μ (K : Set G) * F (ι h) := by
    calc
      _ = ∫⁻ g, χ g * F (ι h * g) ∂μ := by
        have he := lintegral_mul_left_eq_self (μ := μ) (Q h) (ι h)
        simpa only [Q, inv_mul_cancel_left] using he.symm
      _ = ∫⁻ g, χ g * F (ι h) ∂μ := by
        apply lintegral_congr
        intro g
        by_cases hg : g ∈ K
        · rw [hfixed g hg]
        · simp only [χ, Set.indicator_of_notMem hg, zero_mul]
      _ = μ (K : Set G) * F (ι h) := by
        rw [lintegral_mul_const _ hχ]
        simp only [χ, lintegral_indicator hK, lintegral_const,
          Measure.restrict_apply_univ, one_mul]
  have hfiber (x : G) : (∫⁻ h, χ ((ι h)⁻¹ * x) ∂ν) ≤ ν (ι ⁻¹' (K : Set G)) := by
    have hs : MeasurableSet (haarSubgroupFiber ι K x) :=
      hK.preimage (hι.inv.mul_const x)
    have he : (fun h => χ ((ι h)⁻¹ * x)) =
        (haarSubgroupFiber ι K x).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext h
      rfl
    rw [he, lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ, one_mul]
    exact measure_haarSubgroupFiber_le ν ι K x
  calc
    _ = ∫⁻ h, ∫⁻ x, Q h x ∂μ ∂ν := by
      simp_rw [hpoint]
      exact (lintegral_const_mul _ (hF.comp hι)).symm
    _ = ∫⁻ x, ∫⁻ h, Q h x ∂ν ∂μ := lintegral_lintegral_swap hQ.aemeasurable
    _ ≤ ∫⁻ x, ν (ι ⁻¹' (K : Set G)) * F x ∂μ := by
      apply lintegral_mono
      intro x
      simp only [Q]
      have hsec : Measurable (fun h : H => χ ((ι h)⁻¹ * x)) :=
        hχ.comp (hι.inv.mul_const x)
      rw [lintegral_mul_const _ hsec]
      exact mul_le_mul' (hfiber x) le_rfl
    _ = _ := lintegral_const_mul _ hF

/-- Ambient convergence of a right-invariant function supplies actual
subgroup convergence. Both fixed masses have their genuine values. -/
theorem lintegral_subgroup_lt_top_of_right_invariant
    (ι : H →* G) (hι : Measurable ι) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (hKpos : μ (K : Set G) ≠ 0) (hpre : ν (ι ⁻¹' (K : Set G)) ≠ ⊤)
    (F : G → ℝ≥0∞) (hF : Measurable F)
    (hfixed : ∀ k ∈ K, ∀ g, F (g * k) = F g)
    (hi : (∫⁻ x, F x ∂μ) < ⊤) :
    (∫⁻ h, F (ι h) ∂ν) < ⊤ := by
  have hb := lintegral_subgroup_le_of_right_invariant μ ν ι hι K hK F hF hfixed
  have ht : μ (K : Set G) * (∫⁻ h, F (ι h) ∂ν) < ⊤ :=
    hb.trans_lt (ENNReal.mul_lt_top hpre.lt_top hi)
  by_contra hn
  have he : (∫⁻ h, F (ι h) ∂ν) = ⊤ := eq_top_iff.mpr (not_lt.mp hn)
  rw [he, ENNReal.mul_top hKpos] at ht
  exact lt_irrefl _ ht


/-- A genuine complex ambient integrability bound restricts to the actual
subgroup Haar measure under right invariance and the two mass hypotheses. -/
theorem integrable_subgroup_of_right_invariant
    (ι : H →* G) (hι : Measurable ι) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (hKpos : μ (K : Set G) ≠ 0) (hpre : ν (ι ⁻¹' (K : Set G)) ≠ ⊤)
    (f : G → ℂ) (hf : Measurable f)
    (hfixed : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (hi : Integrable f μ) : Integrable (fun h => f (ι h)) ν := by
  refine ⟨(hf.comp hι).aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  exact lintegral_subgroup_lt_top_of_right_invariant μ ν ι hι K hK hKpos hpre
    (fun g => ‖f g‖ₑ) hf.enorm (fun k hk g => congrArg _ (hfixed k hk g))
    (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral)

end Restriction

end Langlands.RankinSelberg
