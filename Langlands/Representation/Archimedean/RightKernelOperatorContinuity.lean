import Langlands.Representation.Archimedean.SmoothOrbitAveraging
import Mathlib.Topology.CompactOpen

/-! # Operator-norm continuity of right translates of compact averages -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section UniformBound

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {R : G →* (E →L[ℂ] E)}

/-- Joint continuity gives a uniform operator bound on each compact subset of the group. -/
theorem IsContinuousRepresentation.exists_opNorm_le_of_isCompact
    (hR : IsContinuousRepresentation R) {K : Set G} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ K, ‖R g‖ ≤ B := by
  let ops : K → E →L[ℂ] E := fun k => R k.val
  obtain ⟨B, hB⟩ := banach_steinhaus (g := ops) fun v => by
    have hv : Continuous (fun g : G => R g v) := hR.comp (continuous_id.prodMk continuous_const)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hv.continuousOn
    exact ⟨C, fun k => hC k.val k.property⟩
  exact ⟨max 0 B, le_max_left _ _, fun g hg => (hB ⟨g, hg⟩).trans (le_max_right _ _)⟩

end UniformBound

namespace DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (μ : Measure Aˣ)
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem right_translate_smoothedOperator (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : Continuous κ) (hc : HasCompactSupport κ) (g : Aˣ) (v : E) :
    smoothedOperator R μ hR κ hκ hc (R g⁻¹ v) =
      ∫ y, κ (g⁻¹ * y⁻¹) • R y v ∂μ := by
  rw [smoothedOperator_apply, smoothedVector,
    ← integral_mul_right_eq_self (fun y : Aˣ => κ (g⁻¹ * y⁻¹) • R y v) g⁻¹]
  apply integral_congr_ae
  filter_upwards with y
  rw [mul_inv_rev, inv_inv, inv_mul_cancel_left, map_mul, mul_apply_eq_comp]

/-- Precomposition of a compact averaging operator by a right translate varies continuously
in operator norm at the identity, for a right-invariant measure. -/
theorem continuousAt_smoothedOperator_comp_inv (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : Continuous κ) (hc : HasCompactSupport κ) :
    ContinuousAt (fun g : Aˣ => (smoothedOperator R μ hR κ hκ hc).comp (R g⁻¹)) 1 := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  obtain ⟨D, hD, hDnhds⟩ := exists_compact_mem_nhds (1 : Aˣ)
  let K := tsupport κ
  let C := K⁻¹ * D⁻¹ ∪ K⁻¹
  have hC : IsCompact C := (hc.inv.mul hD.inv).union hc.inv
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : IsFiniteMeasure (μ.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  let k : Aˣ → C(C, ℂ) := fun g =>
    ⟨fun y => κ (g⁻¹ * (y.val)⁻¹), hκ.comp (continuous_const.mul continuous_subtype_val.inv)⟩
  have hk : Continuous k := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact hκ.comp (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd).inv)
  obtain ⟨B, hB, hbound⟩ := hR.exists_opNorm_le_of_isCompact hC
  let T := smoothedOperator R μ hR κ hκ hc
  have ht : T.comp (R ((1 : Aˣ)⁻¹)) = T := by
    rw [inv_one, map_one]
    exact T.comp_id
  change Tendsto (fun g : Aˣ => T.comp (R g⁻¹)) (𝓝 1) (𝓝 (T.comp (R ((1 : Aˣ)⁻¹))))
  rw [ht, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun g => μ.real C * (‖k g - k 1‖ * B)) (𝓝 1) (𝓝 0) := by
    have hg : Continuous (fun g : Aˣ => μ.real C * (‖k g - k 1‖ * B)) :=
      continuous_const.mul ((hk.sub continuous_const).norm.mul continuous_const)
    simpa only [sub_self, norm_zero, zero_mul, mul_zero] using hg.tendsto 1
  refine squeeze_zero' (Eventually.of_forall fun g => norm_nonneg _) ?_ hlim
  filter_upwards [hDnhds] with g hg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have his (a : Aˣ) : Integrable (fun y => κ (a⁻¹ * y⁻¹) • R y v) μ := by
    have ha : Continuous (fun y : Aˣ => κ (a⁻¹ * y⁻¹)) :=
      hκ.comp (continuous_const.mul continuous_inv)
    have hvs : Continuous (fun y : Aˣ => R y v) := hR.comp (continuous_id.prodMk continuous_const)
    have hks : HasCompactSupport (fun y : Aˣ => κ (a⁻¹ * y⁻¹)) :=
      hc.comp_homeomorph ((Homeomorph.inv Aˣ).trans (Homeomorph.mulLeft a⁻¹))
    exact (ha.smul hvs).integrable_of_hasCompactSupport hks.smul_right
  have hvalue : (T.comp (R g⁻¹) - T) v =
      ∫ y, (κ (g⁻¹ * y⁻¹) - κ y⁻¹) • R y v ∂μ := by
    have hi : Integrable (fun y => κ y⁻¹ • R y v) μ := by simpa using his 1
    change T (R g⁻¹ v) - T v = _
    rw [right_translate_smoothedOperator, smoothedOperator_apply, smoothedVector]
    simp only [sub_smul, integral_sub (his g) hi]
  have hzero (y : Aˣ) (hy : y ∈ Cᶜ) : (κ (g⁻¹ * y⁻¹) - κ y⁻¹) • R y v = 0 := by
    have hy₁ : κ (g⁻¹ * y⁻¹) = 0 := by
      by_contra hn
      apply hy
      apply Or.inl
      exact Set.mem_mul.mpr ⟨(g⁻¹ * y⁻¹)⁻¹, subset_tsupport κ hn, g⁻¹, by simpa,
        by simp [mul_inv_rev, mul_assoc]⟩
    have hy₂ : κ y⁻¹ = 0 := by
      by_contra hn
      exact hy (Or.inr (subset_tsupport κ hn))
    rw [hy₁, hy₂, sub_self, zero_smul]
  rw [hvalue, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ (‖k g - k 1‖ * (B * ‖v‖)) * (μ.restrict C).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem hC.isClosed.measurableSet] with y hy
      rw [norm_smul]
      have hscalar : ‖κ (g⁻¹ * y⁻¹) - κ y⁻¹‖ ≤ ‖k g - k 1‖ := by
        have h := (k g - k 1).norm_coe_le_norm ⟨y, hy⟩
        simpa [k] using h
      have hv := ((R y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hbound y hy) (norm_nonneg v))
      exact mul_le_mul hscalar hv (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [measureReal_restrict_apply_univ]; ring

end DerivativeSmoothVectors
end Langlands.Archimedean
