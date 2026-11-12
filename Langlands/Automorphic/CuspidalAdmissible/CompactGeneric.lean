import Langlands.Automorphic.CuspidalAdmissible.SquareZeroL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure

/-!
# Averaging over right translates on a compact set

For a measure `ν` on a topological group, a compact set `U` with `0 < ν U < ∞` and the
normalized restriction `μ_U = (ν U)⁻¹ ν|_U`, the average `A φ (g) = ∫ φ(g u) dμ_U(u)` of a
continuous function satisfies the Jensen bounds

* `|φ(g) - A φ(g)|² ≤ ∫ |φ(g) - φ(g u)|² dμ_U(u)`,
* `|A φ(g') - A φ(g)|² ≤ ∫ |φ(g' u) - φ(g u)|² dμ_U(u)`,

and its square integral over a set is controlled by the square integrals of the differences
`φ - φ(· u)`, `u ∈ U`. A compact set is covered by finitely many translates `p V` of a
neighbourhood `V` of `1` with `p` in the set.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalAdmissible

/-- `‖a‖² ≤ 2 ‖b‖² + 2 ‖a - b‖²`. -/
theorem enorm_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖ₑ ^ 2 ≤ 2 * ‖b‖ₑ ^ 2 + 2 * ‖a - b‖ₑ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by rw [add_sub_cancel]
      _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
  have h2 : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖b‖ - ‖a - b‖)]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖a‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h2
    _ = 2 * ENNReal.ofReal (‖b‖ ^ 2) + 2 * ENNReal.ofReal (‖a - b‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- The normalized restriction of `ν` to `U`. -/
def avgMeasure (ν : Measure G) (U : Set G) : Measure G := (ν U)⁻¹ • ν.restrict U

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [BorelSpace G] in
theorem isProbabilityMeasure_avgMeasure (ν : Measure G) (U : Set G) (h0 : ν U ≠ 0)
    (htop : ν U ≠ ⊤) : IsProbabilityMeasure (avgMeasure ν U) := by
  constructor
  rw [avgMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The average of `φ` over the right translates `g u`, `u ∈ U`. -/
def average (ν : Measure G) (U : Set G) (φ : G → ℂ) (g : G) : ℂ :=
  ∫ u, φ (g * u) ∂avgMeasure ν U

theorem integrable_translate_avgMeasure (ν : Measure G) [IsFiniteMeasureOnCompacts ν]
    {U : Set G} (hU : IsCompact U) (h0 : ν U ≠ 0) {φ : G → ℂ} (hφ : Continuous φ) (g : G) :
    Integrable (fun u => φ (g * u)) (avgMeasure ν U) := by
  have h : IntegrableOn (fun u => φ (g * u)) U ν :=
    (hφ.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact hU
  exact h.smul_measure (ENNReal.inv_ne_top.mpr h0)

theorem average_add (ν : Measure G) [IsFiniteMeasureOnCompacts ν] {U : Set G}
    (hU : IsCompact U) (h0 : ν U ≠ 0) {φ ψ : G → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (g : G) : average ν U (φ + ψ) g = average ν U φ g + average ν U ψ g :=
  integral_add (integrable_translate_avgMeasure ν hU h0 hφ g)
    (integrable_translate_avgMeasure ν hU h0 hψ g)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [BorelSpace G] in
theorem average_smul (ν : Measure G) (U : Set G) (c : ℂ) (φ : G → ℂ) (g : G) :
    average ν U (c • φ) g = c • average ν U φ g :=
  integral_smul c _

/-- **Jensen for the average.** -/
theorem enorm_sub_average_sq_le (ν : Measure G) [IsFiniteMeasureOnCompacts ν] {U : Set G}
    (hU : IsCompact U) (h0 : ν U ≠ 0) {φ : G → ℂ} (hφ : Continuous φ) (g : G) :
    ‖φ g - average ν U φ g‖ₑ ^ 2 ≤ ∫⁻ u, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂avgMeasure ν U := by
  have htop : ν U ≠ ⊤ := hU.measure_lt_top.ne
  have := isProbabilityMeasure_avgMeasure ν U h0 htop
  have hint := integrable_translate_avgMeasure ν hU h0 hφ g
  have key : φ g - average ν U φ g = ∫ u, (φ g - φ (g * u)) ∂avgMeasure ν U := by
    rw [integral_sub (integrable_const _) hint, integral_const, average]
    simp
  have hc : Continuous fun u => φ g - φ (g * u) :=
    continuous_const.sub (hφ.comp (continuous_const.mul continuous_id))
  rw [key]
  calc ‖∫ u, (φ g - φ (g * u)) ∂avgMeasure ν U‖ₑ ^ 2
      ≤ (∫⁻ u, ‖φ g - φ (g * u)‖ₑ ∂avgMeasure ν U) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := sq_lintegral_le _ hc.enorm.aemeasurable

/-- **Jensen for differences of averages.** -/
theorem enorm_average_sub_sq_le (ν : Measure G) [IsFiniteMeasureOnCompacts ν] {U : Set G}
    (hU : IsCompact U) (h0 : ν U ≠ 0) {φ : G → ℂ} (hφ : Continuous φ) (g g' : G) :
    ‖average ν U φ g' - average ν U φ g‖ₑ ^ 2 ≤
      ∫⁻ u, ‖φ (g' * u) - φ (g * u)‖ₑ ^ 2 ∂avgMeasure ν U := by
  have htop : ν U ≠ ⊤ := hU.measure_lt_top.ne
  have := isProbabilityMeasure_avgMeasure ν U h0 htop
  have key : average ν U φ g' - average ν U φ g =
      ∫ u, (φ (g' * u) - φ (g * u)) ∂avgMeasure ν U :=
    (integral_sub (integrable_translate_avgMeasure ν hU h0 hφ g')
      (integrable_translate_avgMeasure ν hU h0 hφ g)).symm
  have hc : Continuous fun u => φ (g' * u) - φ (g * u) :=
    (hφ.comp (continuous_const.mul continuous_id)).sub
      (hφ.comp (continuous_const.mul continuous_id))
  rw [key]
  calc ‖∫ u, (φ (g' * u) - φ (g * u)) ∂avgMeasure ν U‖ₑ ^ 2
      ≤ (∫⁻ u, ‖φ (g' * u) - φ (g * u)‖ₑ ∂avgMeasure ν U) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := sq_lintegral_le _ hc.enorm.aemeasurable

/-- **Smoothing error.** If every difference `φ - φ(· u)`, `u ∈ U`, has square integral at most
`a` over `Kc`, so has `φ - A φ`. -/
theorem lintegral_sub_average_le [SecondCountableTopology G] (ν : Measure G)
    [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    {U : Set G} (hU : IsCompact U) (h0 : ν U ≠ 0) {φ : G → ℂ} (hφ : Continuous φ)
    (Kc : Set G) (a : ℝ≥0∞)
    (ha : ∀ u ∈ U, ∫⁻ g in Kc, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂ν ≤ a) :
    ∫⁻ g in Kc, ‖φ g - average ν U φ g‖ₑ ^ 2 ∂ν ≤ a := by
  have htop : ν U ≠ ⊤ := hU.measure_lt_top.ne
  have := isProbabilityMeasure_avgMeasure ν U h0 htop
  have hm : Measurable fun p : G × G => ‖φ p.1 - φ (p.1 * p.2)‖ₑ ^ 2 :=
    ((hφ.comp continuous_fst).sub
      (hφ.comp (continuous_fst.mul continuous_snd))).measurable.enorm.pow_const 2
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  calc ∫⁻ g in Kc, ‖φ g - average ν U φ g‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ g in Kc, (∫⁻ u, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂avgMeasure ν U) ∂ν :=
        lintegral_mono fun g => enorm_sub_average_sq_le ν hU h0 hφ g
    _ = ∫⁻ u, (∫⁻ g in Kc, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂ν) ∂avgMeasure ν U :=
        lintegral_lintegral_swap (f := fun g u => ‖φ g - φ (g * u)‖ₑ ^ 2) hm.aemeasurable
    _ ≤ ∫⁻ _u, a ∂avgMeasure ν U := by
        refine lintegral_mono_ae ?_
        have hae : ∀ᵐ u ∂avgMeasure ν U, u ∈ U := by
          unfold avgMeasure
          exact (ae_restrict_mem hUm).filter_mono (Measure.ae_smul_measure_le _)
        filter_upwards [hae] with u hu
        exact ha u hu
    _ = a := by rw [lintegral_const, measure_univ, mul_one]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- A compact set is covered by finitely many translates `p V`, `p` in the set. -/
theorem exists_finite_net {Kc : Set G} (hKc : IsCompact Kc) {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    ∃ s : Finset G, (↑s : Set G) ⊆ Kc ∧ ∀ g ∈ Kc, ∃ p ∈ s, ∃ w ∈ V, g = p * w := by
  obtain ⟨W, hWV, hWo, hW1⟩ := mem_nhds_iff.mp hV
  obtain ⟨s, hs, hcover⟩ := hKc.elim_nhds_subcover (fun p => p • W) fun p _ =>
    (hWo.smul p).mem_nhds (by simpa using Set.smul_mem_smul_set (a := p) hW1)
  refine ⟨s, fun p hp => hs p hp, fun g hg => ?_⟩
  obtain ⟨p, hp, hgp⟩ := Set.mem_iUnion₂.mp (hcover hg)
  obtain ⟨w, hw, rfl⟩ := hgp
  exact ⟨p, hp, w, hWV hw, rfl⟩

omit [T2Space G] in
/-- Right-translate version of `setLIntegral_translates_le`, for a right-invariant measure. -/
theorem setLIntegral_right_translates_le [SecondCountableTopology G] (ν : Measure G)
    [ν.IsMulRightInvariant] [SFinite ν] {ι : Type*} (s : Finset ι) (φ : ι → G → ℂ)
    (hφ : ∀ k, Continuous (φ k)) (u : ℝ → G) (hu : Continuous u) (R t : Set G)
    (hRt : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ g ∈ R, g * u σ ∈ t) :
    ∫⁻ g in R, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, ‖φ k (g * u σ)‖ₑ ^ 2) ∂ν ≤
      ∑ k ∈ s, ∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν := by
  have hm : ∀ k, Measurable fun p : G × ℝ => ‖φ k (p.1 * u p.2)‖ₑ ^ 2 := fun k =>
    ((hφ k).comp (continuous_fst.mul (hu.comp continuous_snd))).measurable.enorm.pow_const 2
  have hm' : Measurable fun p : G × ℝ => ∑ k ∈ s, ‖φ k (p.1 * u p.2)‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun k _ => hm k
  have hslice : ∀ (σ : ℝ) k, Measurable fun g : G => ‖φ k (g * u σ)‖ₑ ^ 2 := fun σ k =>
    ((hφ k).comp (continuous_id.mul continuous_const)).measurable.enorm.pow_const 2
  calc ∫⁻ g in R, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, ‖φ k (g * u σ)‖ₑ ^ 2) ∂ν
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ g in R, ∑ k ∈ s, ‖φ k (g * u σ)‖ₑ ^ 2 ∂ν) :=
        lintegral_lintegral_swap (f := fun g σ => ∑ k ∈ s, ‖φ k (g * u σ)‖ₑ ^ 2)
          hm'.aemeasurable
    _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, (∫⁻ g in R, ‖φ k (g * u σ)‖ₑ ^ 2 ∂ν) :=
        lintegral_congr fun σ => lintegral_finsetSum _ fun k _ => hslice σ k
    _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, (∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν) := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => Finset.sum_le_sum fun k _ => ?_
        rw [(measurePreserving_mul_right ν (u σ)).setLIntegral_comp_emb
          (measurableEmbedding_mulRight (u σ)) (fun g => ‖φ k g‖ₑ ^ 2) R]
        refine lintegral_mono_set ?_
        rintro _ ⟨g, hg, rfl⟩
        exact hRt σ hσ g hg
    _ = ∑ k ∈ s, ∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

end Langlands.Automorphic.CuspidalAdmissible
