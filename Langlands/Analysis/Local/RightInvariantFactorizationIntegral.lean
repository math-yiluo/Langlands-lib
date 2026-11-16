import Langlands.Analysis.Local.CompactFactorizationIntegral

/-!
# Factorization integrals over right-invariant measurable sets

The integrating set need not be the subgroup occurring in `G = ι(X) K`.
It suffices that membership in the set is invariant under right multiplication
by `K`. This permits a positive-measure neighborhood when `K` itself has zero
ambient Haar measure.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory Measure Set
open scoped ENNReal

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableInv G] [MeasurableSpace X]

/-- A set whose membership is unchanged by right multiplication by `K`. -/
def RightSubgroupInvariant (K : Subgroup G) (C : Set G) : Prop :=
  ∀ (g k : G), k ∈ K → (g * k ∈ C ↔ g ∈ C)

/-- Tonelli factorization with an arbitrary measurable right-`K`-invariant set.
The normalizing mass is the measure of the parameters whose inverse lies in `C`. -/
theorem lintegral_rightInvariant_lintegral_mul
    (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (C : Set G) (hC : MeasurableSet C)
    (hCK : RightSubgroupInvariant K C)
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c in C, ∫⁻ x, F (ι x * c) ∂ρ ∂μ =
      ρ {x | (ι x)⁻¹ ∈ C} * ∫⁻ y, F y ∂μ := by
  have hpair : Measurable fun p : X × G => (ι p.1)⁻¹ * p.2 :=
    (hι.comp measurable_fst).inv.mul measurable_snd
  have hS : MeasurableSet {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C} := hpair hC
  have h1 : ∫⁻ c in C, ∫⁻ x, F (ι x * c) ∂ρ ∂μ =
      ∫⁻ x, ∫⁻ c in C, F (ι x * c) ∂μ ∂ρ := by
    apply lintegral_lintegral_swap
    exact (hF.comp ((hι.comp measurable_snd).mul measurable_fst)).aemeasurable
  have h2 (x : X) : ∫⁻ c in C, F (ι x * c) ∂μ =
      ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C}.indicator
        (fun p => F p.2) (x, y) ∂μ := by
    rw [← lintegral_indicator hC]
    rw [← lintegral_mul_left_eq_self _ (ι x)⁻¹]
    apply lintegral_congr
    intro y
    by_cases hy : (ι x)⁻¹ * y ∈ C
    · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C} from hy), mul_inv_cancel_left]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show (x, y) ∉
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C} from hy)]
  have h3 : ∫⁻ x, ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C}.indicator
        (fun p => F p.2) (x, y) ∂μ ∂ρ =
      ∫⁻ y, ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C}.indicator
        (fun p => F p.2) (x, y) ∂ρ ∂μ := by
    apply lintegral_lintegral_swap
    exact ((hF.comp measurable_snd).indicator hS).aemeasurable
  have h4 (y : G) : ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C}.indicator
        (fun p => F p.2) (x, y) ∂ρ = ρ {x | (ι x)⁻¹ ∈ C} * F y := by
    obtain ⟨x₀, k₀, hk₀, rfl⟩ := hfac y
    obtain ⟨σ, hσm, hσι⟩ := hσ x₀
    have hset : {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C} =
        σ ⁻¹' {x : X | (ι x)⁻¹ ∈ C} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, hσι, mul_inv_rev, inv_inv]
      rw [← mul_assoc, hCK _ _ hk₀]
    have hmeas : MeasurableSet {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C} :=
      (hι.inv.mul_const _) hC
    calc
      ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C}.indicator
          (fun p => F p.2) (x, ι x₀ * k₀) ∂ρ =
          ∫⁻ x, {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C}.indicator 1 x *
            F (ι x₀ * k₀) ∂ρ := by
        apply lintegral_congr
        intro x
        by_cases hx : (ι x)⁻¹ * (ι x₀ * k₀) ∈ C
        · rw [indicator_of_mem (show (x, ι x₀ * k₀) ∈
            {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C} from hx),
            indicator_of_mem (show x ∈
              {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C} from hx),
            Pi.one_apply, one_mul]
        · rw [indicator_of_notMem (show (x, ι x₀ * k₀) ∉
            {p : X × G | (ι p.1)⁻¹ * p.2 ∈ C} from hx),
            indicator_of_notMem (show x ∉
              {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C} from hx),
            zero_mul]
      _ = ρ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ C} *
          F (ι x₀ * k₀) := by
        rw [lintegral_mul_const _ (measurable_one.indicator hmeas),
          lintegral_indicator_one hmeas]
      _ = ρ {x | (ι x)⁻¹ ∈ C} * F (ι x₀ * k₀) := by
        have hmassMeas : MeasurableSet {x : X | (ι x)⁻¹ ∈ C} := hι.inv hC
        rw [hset, hσm.measure_preimage hmassMeas.nullMeasurableSet]
  rw [h1]
  simp_rw [h2]
  rw [h3]
  simp_rw [h4]
  rw [lintegral_const_mul _ hF]

/-- A finite, uniform majorant for the parameter integrals over `C` gives a
finite ambient integral, provided the parameter mass of `C` is nonzero. -/
theorem lintegral_lt_top_of_rightInvariant_majorant
    (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (C : Set G) (hC : MeasurableSet C)
    (hCK : RightSubgroupInvariant K C) (hCfinite : μ C < ⊤)
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (hmass : ρ {x | (ι x)⁻¹ ∈ C} ≠ 0)
    (F : G → ℝ≥0∞) (hF : Measurable F)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ c ∈ C, ∫⁻ x, F (ι x * c) ∂ρ ≤ B) :
    ∫⁻ y, F y ∂μ < ⊤ := by
  have hfinite : ∫⁻ c in C, ∫⁻ x, F (ι x * c) ∂ρ ∂μ < ⊤ := by
    calc
      ∫⁻ c in C, ∫⁻ x, F (ι x * c) ∂ρ ∂μ ≤ ∫⁻ _c in C, B ∂μ :=
        setLIntegral_mono' hC hbound
      _ = μ C * B := by simp [mul_comm]
      _ < ⊤ := ENNReal.mul_lt_top hCfinite hB
  rw [lintegral_rightInvariant_lintegral_mul μ K C hC hCK ρ ι hι hfac hσ F hF]
    at hfinite
  exact ENNReal.lt_top_of_mul_ne_top_right hfinite.ne hmass

end Langlands.CompactFactorization
