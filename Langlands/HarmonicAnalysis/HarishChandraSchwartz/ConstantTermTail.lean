import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalDecay

/-! # Rapid tail estimates from the full constant-term estimate

Adding a nonnegative exponent to the ambient height decay extracts the
same negative power of a unipotent tail cutoff. No invariance of the tail
or weights under a compact covering subgroup is required.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [MeasurableSpace G]
  {M U : Subgroup G} {ν : Measure U} {δ : M →* ℝ≥0ˣ}
  {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

/-- The full constant-term estimate with an arbitrary additional negative
power of a height cutoff on an arbitrary unipotent subset. -/
def ConstantTermTailEstimate (ν : Measure U) (δ : M →* ℝ≥0ˣ)
    (Ξ σ : G → ℝ) (ΞM σM : M → ℝ) : Prop :=
  ∀ d p : ℝ, 0 ≤ p →
    ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ (V : Set U) (t : ℝ), 0 < t →
      (∀ u ∈ V, t ≤ 1 + σ u) → ∀ m : M,
        (NNReal.sqrt (δ m) : ℝ≥0∞) *
            ∫⁻ u, V.indicator (fun u : U =>
              ENNReal.ofReal (Ξ ((m : G) * u) *
                (1 + σ ((m : G) * u)) ^ (-d'))) u ∂ν ≤
          c * ENNReal.ofReal (t ^ (-p)) *
            ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))

/-- The full II.4.5 estimate and the II.3.1 height-product bound imply
arbitrary-power tail decay, without compact invariance hypotheses. -/
theorem ConstantTermEstimate.tail
    (h : ConstantTermEstimate ν δ Ξ σ ΞM σM)
    (hΞ : ∀ g, 0 ≤ Ξ g) (hσ : ∀ g, 0 ≤ σ g)
    (hprod : SigmaProductBound M U σ) :
    ConstantTermTailEstimate ν δ Ξ σ ΞM σM := by
  intro d p hp
  obtain ⟨d', c, hc⟩ := h d
  obtain ⟨C, hC, hprod⟩ := hprod
  let D : ℝ≥0 := Real.toNNReal (C ^ (-p))
  have hD : (D : ℝ) = C ^ (-p) := Real.coe_toNNReal _ (Real.rpow_nonneg hC.le _)
  refine ⟨d' + p, c * D, fun V t ht hV m => ?_⟩
  have hct : 0 ≤ C ^ (-p) * t ^ (-p) := by positivity
  have hpt (u : U) (hu : u ∈ V) :
      Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-(d' + p)) ≤
        (C ^ (-p) * t ^ (-p)) *
          (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) := by
    have hb : 0 < 1 + σ ((m : G) * u) := by linarith [hσ ((m : G) * u)]
    have hcut : C * t ≤ 1 + σ ((m : G) * u) :=
      (mul_le_mul_of_nonneg_left
        ((hV u hu).trans (by linarith [le_max_right (σ m) (σ u)])) hC.le).trans
          (hprod m u)
    have hpow : (1 + σ ((m : G) * u)) ^ (-p) ≤ C ^ (-p) * t ^ (-p) := by
      rw [← Real.mul_rpow hC.le ht.le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos hC ht) hcut (neg_nonpos.mpr hp)
    rw [neg_add, Real.rpow_add hb]
    calc
      _ ≤ Ξ ((m : G) * u) *
          ((1 + σ ((m : G) * u)) ^ (-d') * (C ^ (-p) * t ^ (-p))) := by
        gcongr
        exact hΞ _
      _ = _ := by ring
  have hint :
      ∫⁻ u, V.indicator (fun u : U => ENNReal.ofReal
          (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-(d' + p)))) u ∂ν ≤
        ENNReal.ofReal (C ^ (-p) * t ^ (-p)) *
          ∫⁻ u : U, ENNReal.ofReal
            (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun u => ?_
    by_cases hu : u ∈ V
    · rw [Set.indicator_of_mem hu, ← ENNReal.ofReal_mul hct]
      exact ENNReal.ofReal_le_ofReal (hpt u hu)
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  calc
    (NNReal.sqrt (δ m) : ℝ≥0∞) * _ ≤
        (NNReal.sqrt (δ m) : ℝ≥0∞) *
          (ENNReal.ofReal (C ^ (-p) * t ^ (-p)) *
            ∫⁻ u : U, ENNReal.ofReal
              (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν) := by
      gcongr
    _ = ENNReal.ofReal (C ^ (-p) * t ^ (-p)) *
        ((NNReal.sqrt (δ m) : ℝ≥0∞) *
          ∫⁻ u : U, ENNReal.ofReal
            (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-d')) ∂ν) := by ring
    _ ≤ ENNReal.ofReal (C ^ (-p) * t ^ (-p)) *
        (c * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d))) := by
      exact mul_le_mul_of_nonneg_left (hc m) zero_le
    _ = (c * D : ℝ≥0) * ENNReal.ofReal (t ^ (-p)) *
        ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-d)) := by
      rw [ENNReal.coe_mul, ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _),
        ← hD, ENNReal.ofReal_coe_nnreal]
      ring

end Langlands.HarishChandraSchwartz
