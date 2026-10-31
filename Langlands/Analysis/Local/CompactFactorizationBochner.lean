import Langlands.Analysis.Local.CompactFactorizationIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Pushforward and Bochner forms of the factorization integral

For a factorization `G = ι(X) K` as in `CompactFactorizationIntegral`, the
pushforward of `μ|_K × ρ` under `(k, x) ↦ ι x * k` is `ρ (ι ⁻¹' K) • μ`. Hence
integrability and Bochner integrals transfer between `G` and `K × X`.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory Measure Set
open scoped ENNReal

variable {G X : Type*} [Group G]

/-- The factorization map `(k, x) ↦ ι x * k` from `G × X` to `G`. -/
def factorizationMap (ι : X → G) (p : G × X) : G := ι p.2 * p.1

@[simp] theorem factorizationMap_apply (ι : X → G) (k : G) (x : X) :
    factorizationMap ι (k, x) = ι x * k := rfl

theorem factorizationMap_eq (ι : X → G) :
    factorizationMap ι = fun p : G × X => ι p.2 * p.1 := rfl

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace X]

/-- The factorization map `(k, x) ↦ ι x * k` pushes `μ|_K × ρ` forward to the
multiple `ρ (ι ⁻¹' K) • μ` of the left-invariant measure. -/
theorem map_restrict_prod_mul (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x) :
    ((μ.restrict K).prod ρ).map (factorizationMap ι) = ρ (ι ⁻¹' K) • μ := by
  rw [factorizationMap_eq]
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  ext A hA
  rw [map_apply hφ hA, Measure.smul_apply, smul_eq_mul]
  have hind : MeasurableSet ((fun p : G × X => ι p.2 * p.1) ⁻¹' A) := hφ hA
  rw [← lintegral_indicator_one hind, lintegral_prod _
    ((measurable_one.indicator hind).aemeasurable)]
  have h := lintegral_restrict_lintegral_mul μ K hK ρ ι hι hfac hσ
    (A.indicator 1) (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA] at h
  rw [← h]
  apply lintegral_congr
  intro k
  apply lintegral_congr
  intro x
  by_cases hx : ι x * k ∈ A
  · rw [indicator_of_mem (show (k, x) ∈ (fun p : G × X => ι p.2 * p.1) ⁻¹' A from hx),
      indicator_of_mem hx, Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem (show (k, x) ∉ (fun p : G × X => ι p.2 * p.1) ⁻¹' A from hx),
      indicator_of_notMem hx]

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability transfers between `G` and the factorization coordinates. -/
theorem integrable_comp_mul_iff (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (hpos : ρ (ι ⁻¹' K) ≠ 0) (hfin : ρ (ι ⁻¹' K) ≠ ∞)
    {F : G → E} (hF : AEStronglyMeasurable F μ) :
    Integrable (fun p : G × X => F (ι p.2 * p.1)) ((μ.restrict K).prod ρ) ↔
      Integrable F μ := by
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  have hmap := map_restrict_prod_mul μ K hK ρ ι hι hfac hσ
  rw [factorizationMap_eq] at hmap
  have hF' : AEStronglyMeasurable F
      (((μ.restrict K).prod ρ).map (fun p : G × X => ι p.2 * p.1)) := by
    rw [hmap]
    exact hF.smul_measure _
  have h := integrable_map_measure hF' hφ.aemeasurable
  rw [hmap, integrable_smul_measure hpos hfin] at h
  exact h.symm

/-- **Bochner factorization integral.** For an integrable function on `G`, the
iterated integral over `K` and the parameter space is `ρ (ι ⁻¹' K)` times the
integral over `G`. -/
theorem integral_restrict_integral_mul [NormedSpace ℝ E] (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (hpos : ρ (ι ⁻¹' K) ≠ 0) (hfin : ρ (ι ⁻¹' K) ≠ ∞)
    {F : G → E} (hF : Integrable F μ) :
    ∫ k in (K : Set G), ∫ x, F (ι x * k) ∂ρ ∂μ = (ρ (ι ⁻¹' K)).toReal • ∫ y, F y ∂μ := by
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  have hmap := map_restrict_prod_mul μ K hK ρ ι hι hfac hσ
  rw [factorizationMap_eq] at hmap
  have hint := (integrable_comp_mul_iff μ K hK ρ ι hι hfac hσ hpos hfin
    hF.aestronglyMeasurable).mpr hF
  have hF' : AEStronglyMeasurable F
      (((μ.restrict K).prod ρ).map (fun p : G × X => ι p.2 * p.1)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable.smul_measure _
  rw [← integral_smul_measure, ← hmap, integral_map hφ.aemeasurable hF']
  exact (integral_prod (fun p : G × X => F (ι p.2 * p.1)) hint).symm


/-! ### Functions supported in `ι(X) K` -/

/-- **Factorization integral on a support.** If `F` vanishes off `ι(X) K`, the
factorization identity holds without assuming `G = ι(X) K`. -/
theorem lintegral_restrict_lintegral_mul_of_support (μ : Measure G) [SFinite μ]
    [IsMulLeftInvariant μ] (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (F : G → ℝ≥0∞) (hF : Measurable F)
    (hsupp : ∀ y : G, F y ≠ 0 → ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀) :
    ∫⁻ k in (K : Set G), ∫⁻ x, F (ι x * k) ∂ρ ∂μ = ρ (ι ⁻¹' K) * ∫⁻ y, F y ∂μ := by
  have hpair : Measurable fun p : X × G => (ι p.1)⁻¹ * p.2 :=
    (hι.comp measurable_fst).inv.mul measurable_snd
  have hS : MeasurableSet {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} := hpair hK
  have h1 : ∫⁻ k in (K : Set G), ∫⁻ x, F (ι x * k) ∂ρ ∂μ =
      ∫⁻ x, ∫⁻ k in (K : Set G), F (ι x * k) ∂μ ∂ρ := by
    apply lintegral_lintegral_swap
    exact (hF.comp ((hι.comp measurable_snd).mul measurable_fst)).aemeasurable
  have h2 (x : X) : ∫⁻ k in (K : Set G), F (ι x * k) ∂μ =
      ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator (fun p => F p.2) (x, y) ∂μ := by
    rw [← lintegral_indicator hK]
    rw [← lintegral_mul_left_eq_self _ (ι x)⁻¹]
    apply lintegral_congr
    intro y
    by_cases hy : (ι x)⁻¹ * y ∈ K
    · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hy), mul_inv_cancel_left]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show (x, y) ∉
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hy)]
  have h3 : ∫⁻ x, ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂μ ∂ρ =
      ∫⁻ y, ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂ρ ∂μ := by
    apply lintegral_lintegral_swap
    exact ((hF.comp measurable_snd).indicator hS).aemeasurable
  have h4 (y : G) : ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂ρ = ρ (ι ⁻¹' K) * F y := by
    by_cases hy : F y = 0
    · rw [hy, mul_zero]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with x
      by_cases hx : (x, y) ∈ {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}
      · rw [indicator_of_mem hx, hy, Pi.zero_apply]
      · rw [indicator_of_notMem hx, Pi.zero_apply]
    obtain ⟨x₀, k₀, hk₀, rfl⟩ := hsupp y hy
    obtain ⟨σ, hσm, hσι⟩ := hσ x₀
    have hset : {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} = σ ⁻¹' (ι ⁻¹' K) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, hσι]
      rw [← mul_assoc, Subgroup.mul_mem_cancel_right K hk₀, ← inv_mem_iff (H := K)]
      simp only [mul_inv_rev, inv_inv]
    have hmeas : MeasurableSet {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} :=
      ((hι.inv.mul_const _) hK)
    calc ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator (fun p => F p.2)
            (x, ι x₀ * k₀) ∂ρ
        = ∫⁻ x, {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K}.indicator 1 x * F (ι x₀ * k₀) ∂ρ := by
          apply lintegral_congr
          intro x
          by_cases hx : (ι x)⁻¹ * (ι x₀ * k₀) ∈ K
          · rw [indicator_of_mem (show (x, ι x₀ * k₀) ∈
              {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hx),
              indicator_of_mem (show x ∈ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} from hx),
              Pi.one_apply, one_mul]
          · rw [indicator_of_notMem (show (x, ι x₀ * k₀) ∉
              {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hx),
              indicator_of_notMem (show x ∉ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} from hx),
              zero_mul]
      _ = ρ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} * F (ι x₀ * k₀) := by
          rw [lintegral_mul_const _ (measurable_one.indicator hmeas),
            lintegral_indicator_one hmeas]
      _ = ρ (ι ⁻¹' K) * F (ι x₀ * k₀) := by
          rw [hset, hσm.measure_preimage (hι hK).nullMeasurableSet]
  rw [h1]
  simp_rw [h2]
  rw [h3]
  simp_rw [h4]
  rw [lintegral_const_mul _ hF]

/-- On a measurable set `S = ι(X) K`, the factorization map pushes `μ|_K × ρ`
forward to `ρ (ι ⁻¹' K) • μ|_S`. -/
theorem map_restrict_prod_mul_of_subset (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (S : Set G) (hS : MeasurableSet S)
    (hSfac : ∀ y ∈ S, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hSK : ∀ x : X, ∀ k ∈ K, ι x * k ∈ S) :
    ((μ.restrict K).prod ρ).map (factorizationMap ι) =
      ρ (ι ⁻¹' K) • μ.restrict S := by
  rw [factorizationMap_eq]
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  ext A hA
  rw [map_apply hφ hA, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  have hind : MeasurableSet ((fun p : G × X => ι p.2 * p.1) ⁻¹' A) := hφ hA
  rw [← lintegral_indicator_one hind, lintegral_prod _
    ((measurable_one.indicator hind).aemeasurable)]
  have h := lintegral_restrict_lintegral_mul_of_support μ K hK ρ ι hι hσ
    ((A ∩ S).indicator 1) (measurable_one.indicator (hA.inter hS)) (by
      intro y hy
      have hyS : y ∈ A ∩ S := by
        by_contra hn
        exact hy (indicator_of_notMem hn _)
      exact hSfac y hyS.2)
  rw [lintegral_indicator_one (hA.inter hS)] at h
  rw [← h]
  apply setLIntegral_congr_fun hK
  intro k hk
  apply lintegral_congr
  intro x
  have hxS : ι x * k ∈ S := hSK x k hk
  by_cases hx : ι x * k ∈ A
  · rw [indicator_of_mem (show (k, x) ∈ (fun p : G × X => ι p.2 * p.1) ⁻¹' A from hx),
      indicator_of_mem (show ι x * k ∈ A ∩ S from ⟨hx, hxS⟩), Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem (show (k, x) ∉ (fun p : G × X => ι p.2 * p.1) ⁻¹' A from hx),
      indicator_of_notMem (show ι x * k ∉ A ∩ S from fun h => hx h.1)]

/-- Integrability transfer for functions on `ι(X) K`. -/
theorem integrable_comp_mul_iff_of_subset (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (S : Set G) (hS : MeasurableSet S)
    (hSfac : ∀ y ∈ S, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hSK : ∀ x : X, ∀ k ∈ K, ι x * k ∈ S)
    (hpos : ρ (ι ⁻¹' K) ≠ 0) (hfin : ρ (ι ⁻¹' K) ≠ ∞)
    {F : G → E} (hF : AEStronglyMeasurable F μ) :
    Integrable (fun p : G × X => F (ι p.2 * p.1)) ((μ.restrict K).prod ρ) ↔
      Integrable F (μ.restrict S) := by
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  have hmap := map_restrict_prod_mul_of_subset μ K hK ρ ι hι hσ S hS hSfac hSK
  rw [factorizationMap_eq] at hmap
  have hF' : AEStronglyMeasurable F
      (((μ.restrict K).prod ρ).map (fun p : G × X => ι p.2 * p.1)) := by
    rw [hmap]
    exact hF.restrict.smul_measure _
  have h := integrable_map_measure hF' hφ.aemeasurable
  rw [hmap, integrable_smul_measure hpos hfin] at h
  exact h.symm

/-- **Bochner factorization integral on `ι(X) K`.** -/
theorem integral_restrict_integral_mul_of_subset [NormedSpace ℝ E] (μ : Measure G) [SFinite μ]
    [IsMulLeftInvariant μ] (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (S : Set G) (hS : MeasurableSet S)
    (hSfac : ∀ y ∈ S, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hSK : ∀ x : X, ∀ k ∈ K, ι x * k ∈ S)
    (hpos : ρ (ι ⁻¹' K) ≠ 0) (hfin : ρ (ι ⁻¹' K) ≠ ∞)
    {F : G → E} (hF : Integrable F (μ.restrict S)) :
    ∫ k in (K : Set G), ∫ x, F (ι x * k) ∂ρ ∂μ =
      (ρ (ι ⁻¹' K)).toReal • ∫ y in S, F y ∂μ := by
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  have hmap := map_restrict_prod_mul_of_subset μ K hK ρ ι hι hσ S hS hSfac hSK
  rw [factorizationMap_eq] at hmap
  have hF' : AEStronglyMeasurable F
      (((μ.restrict K).prod ρ).map (fun p : G × X => ι p.2 * p.1)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable.smul_measure _
  have hint : Integrable (fun p : G × X => F (ι p.2 * p.1)) ((μ.restrict K).prod ρ) := by
    have h := integrable_map_measure hF' hφ.aemeasurable
    rw [hmap, integrable_smul_measure hpos hfin] at h
    exact h.mp hF
  rw [← integral_smul_measure, ← hmap, integral_map hφ.aemeasurable hF']
  exact (integral_prod (fun p : G × X => F (ι p.2 * p.1)) hint).symm


/-! ### Integrals of compact coefficient formulas

A function of the form `g ↦ H g * ∫ k, Γ k (j k * g) ∂ν` arises from a zeta
integrand `H` and a coefficient given by an integral over a compact group. The
substitution `g ↦ j k * g` turns its integral into an integral over the product
of `Ψ (k, y) = H ((j k)⁻¹ * y) * Γ k y`. -/

section CoefficientIntegrals

variable {κ κ' : Type*} [MeasurableSpace κ] [MeasurableSpace κ']

omit [MeasurableInv G] in
/-- **Substitution in a compact coefficient integral.** If the function
`(k, y) ↦ H ((j k)⁻¹ * y) * Γ k y` is integrable, then
`g ↦ H g * ∫ k, Γ k (j k * g) ∂ν` is integrable with the same integral. -/
theorem integrable_integral_coefficient_of_integrable (μ : Measure G) [SFinite μ]
    [IsMulLeftInvariant μ] (ν : Measure κ) [SFinite ν] (j : κ → G) (hj : Measurable j)
    (H : G → ℂ) (Γ : κ → G → ℂ)
    (hΨ : Integrable (fun z : κ × G => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ)) :
    Integrable (fun g => H g * ∫ k, Γ k (j k * g) ∂ν) μ ∧
      ∫ g, H g * ∫ k, Γ k (j k * g) ∂ν ∂μ =
        ∫ z, H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2 ∂(ν.prod μ) := by
  have hS : MeasurePreserving (fun z : κ × G => (id z.1, j z.1 * z.2))
      (ν.prod μ) (ν.prod μ) :=
    MeasurePreserving.skew_product (MeasurePreserving.id ν)
      (by exact (hj.comp measurable_fst).mul measurable_snd)
      (Filter.Eventually.of_forall fun k => map_mul_left_eq_self μ (j k))
  have hcomp : (fun z : κ × G => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2) ∘
      (fun z : κ × G => (id z.1, j z.1 * z.2)) =
      fun z : κ × G => H z.2 * Γ z.1 (j z.1 * z.2) := by
    funext z
    simp only [Function.comp_apply, id_eq, inv_mul_cancel_left]
  have hint : Integrable (fun z : κ × G => H z.2 * Γ z.1 (j z.1 * z.2)) (ν.prod μ) := by
    rw [← hcomp]
    exact hS.integrable_comp_of_integrable hΨ
  have hfun : (fun g => H g * ∫ k, Γ k (j k * g) ∂ν) =
      fun g => ∫ k, H g * Γ k (j k * g) ∂ν := by
    funext g
    rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hint.integral_prod_right
  · rw [hfun, ← integral_prod_symm _ hint, ← hcomp]
    have hm : AEStronglyMeasurable (fun z : κ × G => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2)
        ((ν.prod μ).map (fun z : κ × G => (id z.1, j z.1 * z.2))) := by
      rw [hS.map_eq]
      exact hΨ.aestronglyMeasurable
    have h := integral_map hS.measurable.aemeasurable hm
    rw [hS.map_eq] at h
    exact h.symm

/-- The map `(k, (k', x)) ↦ (k, ι x * j' k')` pushes `ν × (ν' × ρ)` forward to
`ρ (ι ⁻¹' K) • (ν × μ)` when `j'` pushes `ν'` to `μ|_K`. -/
theorem map_prod_prod_factorization (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (ν : Measure κ) [SFinite ν] (ν' : Measure κ') [SFinite ν'] (j' : κ' → G)
    (hj' : Measurable j') (hν' : ν'.map j' = μ.restrict K) :
    (ν.prod (ν'.prod ρ)).map (fun z : κ × (κ' × X) => (z.1, ι z.2.2 * j' z.2.1)) =
      ρ (ι ⁻¹' K) • ν.prod μ := by
  have hφ : Measurable fun p : G × X => ι p.2 * p.1 :=
    (hι.comp measurable_snd).mul measurable_fst
  have h1 : (ν'.prod ρ).map (fun w : κ' × X => ι w.2 * j' w.1) = ρ (ι ⁻¹' K) • μ := by
    have he : (fun w : κ' × X => ι w.2 * j' w.1) =
        (fun p : G × X => ι p.2 * p.1) ∘ Prod.map j' id := rfl
    rw [he, ← map_map hφ (hj'.prodMap measurable_id),
      ← map_prod_map _ _ hj' measurable_id, hν', Measure.map_id]
    have h := map_restrict_prod_mul μ K hK ρ ι hι hfac hσ
    rw [factorizationMap_eq] at h
    exact h
  have he : (fun z : κ × (κ' × X) => (z.1, ι z.2.2 * j' z.2.1)) =
      Prod.map id (fun w : κ' × X => ι w.2 * j' w.1) := rfl
  have hψ : Measurable fun w : κ' × X => ι w.2 * j' w.1 :=
    (hι.comp measurable_snd).mul (hj'.comp measurable_fst)
  rw [he, ← map_prod_map ν (ν'.prod ρ) measurable_id hψ, Measure.map_id, h1,
    Measure.prod_smul_right]

/-- **Coefficient integrals from a factorized expansion.** Suppose that, for
`k` in the coefficient parameter space and `k'` in a parametrization of `K`,
`H ((j k)⁻¹ * (ι x * j' k')) * Γ k (ι x * j' k')` is a finite sum of products
`ψ r k k' * Q r x` with integrable factors. Then
`g ↦ H g * ∫ k, Γ k (j k * g) ∂ν` is integrable and its integral is
`ρ (ι ⁻¹' K)⁻¹ * ∑ r, (∫ ψ r) * ∫ Q r`. -/
theorem integrable_integral_coefficient_of_expansion (μ : Measure G) [SFinite μ]
    [IsMulLeftInvariant μ] (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (hpos : ρ (ι ⁻¹' K) ≠ 0) (hfin : ρ (ι ⁻¹' K) ≠ ∞)
    (ν : Measure κ) [SFinite ν] (j : κ → G) (hj : Measurable j)
    (ν' : Measure κ') [SFinite ν'] (j' : κ' → G) (hj' : Measurable j')
    (hν' : ν'.map j' = μ.restrict K)
    (H : G → ℂ) (Γ : κ → G → ℂ)
    (hm : AEStronglyMeasurable (fun z : κ × G => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ))
    {R : Type*} (s : Finset R) (ψ : R → κ → κ' → ℂ) (Q : R → X → ℂ)
    (hψ : ∀ r ∈ s, Integrable (fun z : κ × κ' => ψ r z.1 z.2) (ν.prod ν'))
    (hQ : ∀ r ∈ s, Integrable (Q r) ρ)
    (hexp : ∀ k k' x, H ((j k)⁻¹ * (ι x * j' k')) * Γ k (ι x * j' k') =
      ∑ r ∈ s, ψ r k k' * Q r x) :
    Integrable (fun g => H g * ∫ k, Γ k (j k * g) ∂ν) μ ∧
      ∫ g, H g * ∫ k, Γ k (j k * g) ∂ν ∂μ =
        ((ρ (ι ⁻¹' K)).toReal)⁻¹ •
          ∑ r ∈ s, (∫ z, ψ r z.1 z.2 ∂(ν.prod ν')) * ∫ x, Q r x ∂ρ := by
  set Ψ : κ × G → ℂ := fun z => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2 with hΨdef
  set T : κ × (κ' × X) → κ × G := fun z => (z.1, ι z.2.2 * j' z.2.1) with hTdef
  have hT : Measurable T :=
    measurable_fst.prodMk ((hι.comp (measurable_snd.comp measurable_snd)).mul
      (hj'.comp (measurable_fst.comp measurable_snd)))
  have hmap : (ν.prod (ν'.prod ρ)).map T = ρ (ι ⁻¹' K) • ν.prod μ :=
    map_prod_prod_factorization μ K hK ρ ι hι hfac hσ ν ν' j' hj' hν'
  have hcomp : Ψ ∘ T = fun z => ∑ r ∈ s, ψ r z.1 z.2.1 * Q r z.2.2 := by
    funext z
    exact hexp z.1 z.2.1 z.2.2
  have hassoc := measurePreserving_prodAssoc ν ν' ρ
  have hterm (r : R) (hr : r ∈ s) :
      Integrable (fun z : κ × (κ' × X) => ψ r z.1 z.2.1 * Q r z.2.2)
        (ν.prod (ν'.prod ρ)) := by
    rw [← hassoc.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding]
    exact (hψ r hr).mul_prod (hQ r hr)
  have hTint : Integrable (Ψ ∘ T) (ν.prod (ν'.prod ρ)) := by
    rw [hcomp]
    exact integrable_finsetSum s hterm
  have hm' : AEStronglyMeasurable Ψ ((ν.prod (ν'.prod ρ)).map T) := by
    rw [hmap]
    exact hm.smul_measure _
  have hΨint : Integrable Ψ (ν.prod μ) := by
    have h := integrable_map_measure hm' hT.aemeasurable
    rw [hmap, integrable_smul_measure hpos hfin] at h
    exact h.mpr hTint
  obtain ⟨h1, h2⟩ := integrable_integral_coefficient_of_integrable μ ν j hj H Γ hΨint
  refine ⟨h1, ?_⟩
  rw [h2]
  have hc : (ρ (ι ⁻¹' K)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩
  have hval : ∫ z, Ψ z ∂(ν.prod μ) =
      ((ρ (ι ⁻¹' K)).toReal)⁻¹ • ∫ z, Ψ z ∂(ρ (ι ⁻¹' K) • ν.prod μ) := by
    rw [integral_smul_measure, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hval, ← hmap, integral_map hT.aemeasurable hm']
  congr 1
  change ∫ z, (Ψ ∘ T) z ∂(ν.prod (ν'.prod ρ)) = _
  rw [hcomp, integral_finsetSum s hterm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← hassoc.integral_comp' (fun z : κ × (κ' × X) => ψ r z.1 z.2.1 * Q r z.2.2)]
  exact integral_prod_mul (fun z : κ × κ' => ψ r z.1 z.2) (Q r)

omit [MeasurableInv G] in
/-- **Coefficient integrals from translates.** If each slice
`y ↦ H ((j k)⁻¹ * y) * Γ k y` is a left translate of one integrable `Ψ₀` for
`k ∈ S` and vanishes for `k ∉ S`, then the coefficient integral is
`ν S • ∫ Ψ₀`. -/
theorem integrable_integral_coefficient_of_translate (μ : Measure G) [SFinite μ]
    [IsMulLeftInvariant μ] (ν : Measure κ) [IsFiniteMeasure ν] (j : κ → G) (hj : Measurable j)
    (H : G → ℂ) (Γ : κ → G → ℂ)
    (hm : AEStronglyMeasurable (fun z : κ × G => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ))
    (S : Set κ) (hS : MeasurableSet S) (Ψ₀ : G → ℂ) (hΨ₀ : Integrable Ψ₀ μ)
    (htrans : ∀ k ∈ S, ∃ g₀ : G, ∀ y, H ((j k)⁻¹ * y) * Γ k y = Ψ₀ (g₀ * y))
    (hzero : ∀ k ∉ S, ∀ y, H ((j k)⁻¹ * y) * Γ k y = 0) :
    Integrable (fun g => H g * ∫ k, Γ k (j k * g) ∂ν) μ ∧
      ∫ g, H g * ∫ k, Γ k (j k * g) ∂ν ∂μ = (ν S).toReal • ∫ y, Ψ₀ y ∂μ := by
  set Ψ : κ × G → ℂ := fun z => H ((j z.1)⁻¹ * z.2) * Γ z.1 z.2 with hΨdef
  have hslice (k : κ) : ∫ y, Ψ (k, y) ∂μ = S.indicator (fun _ => ∫ y, Ψ₀ y ∂μ) k := by
    by_cases hk : k ∈ S
    · obtain ⟨g₀, hg₀⟩ := htrans k hk
      rw [indicator_of_mem hk]
      simp only [hΨdef, hg₀]
      exact integral_mul_left_eq_self Ψ₀ g₀
    · rw [indicator_of_notMem hk]
      simp only [hΨdef, hzero k hk]
      exact integral_zero _ _
  have hslice_norm (k : κ) :
      ∫ y, ‖Ψ (k, y)‖ ∂μ = S.indicator (fun _ => ∫ y, ‖Ψ₀ y‖ ∂μ) k := by
    by_cases hk : k ∈ S
    · obtain ⟨g₀, hg₀⟩ := htrans k hk
      rw [indicator_of_mem hk]
      simp only [hΨdef, hg₀]
      exact integral_mul_left_eq_self (fun y => ‖Ψ₀ y‖) g₀
    · rw [indicator_of_notMem hk]
      simp only [hΨdef, hzero k hk, norm_zero]
      exact integral_zero _ _
  have hΨint : Integrable Ψ (ν.prod μ) := by
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun k => ?_, ?_⟩
    · by_cases hk : k ∈ S
      · obtain ⟨g₀, hg₀⟩ := htrans k hk
        simp only [hΨdef, hg₀]
        exact hΨ₀.comp_mul_left g₀
      · simp only [hΨdef, hzero k hk]
        exact integrable_zero _ _ _
    · simp only [hslice_norm]
      exact (integrable_const _).indicator hS
  obtain ⟨h1, h2⟩ := integrable_integral_coefficient_of_integrable μ ν j hj H Γ hΨint
  refine ⟨h1, ?_⟩
  rw [h2, integral_prod _ hΨint]
  simp only [hslice]
  rw [integral_indicator_const _ hS]
  rfl

end CoefficientIntegrals

end Langlands.CompactFactorization
