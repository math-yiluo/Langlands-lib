import Langlands.Representation.Archimedean.CompactPowerLocalization
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Recovering the compact subgroup average with invariant weights -/

open Filter MeasureTheory MeasureTheory.Measure Set

open scoped Topology

set_option autoImplicit false

namespace Langlands.Archimedean

universe u v

/-- Nonnegative integrals against the powers of a subgroup-invariant weight
force a nonnegative average over the subgroup on which the weight is one. -/
def CompactSubgroupPowerLocalizationStatement : Prop :=
  ∀ {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ι : H →* K) (μ : Measure K) (ν : Measure H)
    [IsFiniteMeasure μ] [IsOpenPosMeasure μ] [IsMulLeftInvariant μ]
    [IsProbabilityMeasure ν] [IsMulRightInvariant ν]
    {p f : K → ℝ}, Continuous ι → Continuous p → Continuous f →
    (∀ k, p k ∈ Icc 0 1) →
    (∀ k, p k = 1 ↔ k ∈ range ι) →
    (∀ h k, p (ι h * k) = p k) →
    (∀ m : ℕ, 0 ≤ ∫ k, p k ^ m * f k ∂μ) →
    0 ≤ ∫ h, f (ι h) ∂ν

theorem compactSubgroupPowerLocalization : CompactSubgroupPowerLocalizationStatement.{u, v} := by
  intro K _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ ι μ ν _ _ _ _ _ p f hι hp hf hRange hLevel hInv hInt
  let average : K → ℝ := fun k => ∫ h, f (ι h * k) ∂ν
  have hAverage : Continuous average := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    apply continuous_iff_continuousAt.mpr
    intro k
    exact continuousAt_of_dominated (bound := fun _ => M)
      (Eventually.of_forall fun k' =>
        (hf.comp (hι.mul continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun k' => ae_of_all _ fun h => hM (ι h * k') (mem_univ _))
      (integrable_const _)
      (ae_of_all _ fun h => (hf.comp (continuous_const.mul continuous_id)).continuousAt)
  have hAverageInv (h : H) (k : K) : average (ι h * k) = average k := by
    simpa only [average, map_mul, mul_assoc] using
      integral_mul_right_eq_self (μ := ν) (fun h' => f (ι h' * k)) h
  have haverageInt (m : ℕ) :
      (∫ k, p k ^ m * average k ∂μ) = ∫ k, p k ^ m * f k ∂μ := by
    have hcont : Continuous (fun z : K × H => p z.1 ^ m * f (ι z.2 * z.1)) :=
      ((hp.comp continuous_fst).pow m).mul (hf.comp ((hι.comp continuous_snd).mul continuous_fst))
    have hprod : Integrable (fun z : K × H => p z.1 ^ m * f (ι z.2 * z.1)) (μ.prod ν) :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmul (h : H) :
        (∫ k, p k ^ m * f (ι h * k) ∂μ) = ∫ k, p k ^ m * f k ∂μ := by
      simpa only [hInv h] using
        integral_mul_left_eq_self (μ := μ) (fun k => p k ^ m * f k) (ι h)
    simp_rw [average, ← integral_const_mul]
    rw [integral_integral_swap hprod]
    simp [hmul]
  have hOne : p 1 = 1 := (hLevel 1).2 ⟨1, map_one ι⟩
  have hConst (k : K) (hk : p k = 1) : average k = average 1 := by
    obtain ⟨h, rfl⟩ := (hLevel k).1 hk
    simpa only [mul_one] using hAverageInv h 1
  have hNonneg : 0 ≤ average 1 :=
    compactPowerLocalization μ hp hAverage hRange hOne hConst fun m =>
      (haverageInt m).symm ▸ hInt m
  simpa only [average, mul_one] using hNonneg

end Langlands.Archimedean
