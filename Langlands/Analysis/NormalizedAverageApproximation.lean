import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Normalized averages near a point and right invariance under compact subgroups -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise

set_option autoImplicit false

namespace Langlands.Analysis.NormalizedAverage

/-- A Bochner integral of vectors of a closed submodule lies in the submodule. -/
theorem integral_mem_of_isClosed {Y E : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (A : Submodule ℂ E) (hA : IsClosed (A : Set E))
    {f : Y → E} (hf : Integrable f ν) (hfA : ∀ y, f y ∈ A) : (∫ y, f y ∂ν) ∈ A := by
  let : IsClosed (A : Set E) := hA
  apply (Submodule.Quotient.mk_eq_zero A).mp
  change A.mkQL (∫ y, f y ∂ν) = 0
  rw [← A.mkQL.integral_comp_comm hf]
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y =>
    (Submodule.Quotient.mk_eq_zero A).mpr (hfA y))

section Average

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A weighted average with weight of integral one and of absolute integral one stays within
`ε` of `v` when every point where the weight is nonzero has value within `ε` of `v`. -/
theorem norm_integral_smul_sub_le (a : Y → ℂ) (o : Y → E) (v : E) {ε : ℝ}
    (hao : Integrable (fun y => a y • o y) μ) (ha : Integrable a μ)
    (ha1 : (∫ y, a y ∂μ) = 1) (hn : (∫ y, ‖a y‖ ∂μ) = 1)
    (hε : ∀ y, a y ≠ 0 → ‖o y - v‖ ≤ ε) :
    ‖(∫ y, a y • o y ∂μ) - v‖ ≤ ε := by
  have h2 : Integrable (fun y => a y • v) μ := ha.smul_const v
  have heq : (∫ y, a y • o y ∂μ) - v = ∫ y, a y • (o y - v) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hao h2, integral_smul_const, ha1, one_smul]
  rw [heq]
  calc ‖∫ y, a y • (o y - v) ∂μ‖ ≤ ∫ y, ‖a y‖ * ε ∂μ :=
        norm_integral_le_of_norm_le (ha.norm.mul_const ε) (Eventually.of_forall fun y => by
          by_cases hy : a y = 0
          · simp [hy]
          · rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hε y hy) (norm_nonneg _))
    _ = ε := by rw [integral_mul_const, hn, one_mul]

/-- A normalized average of a vector-valued function close to a nonzero vector is nonzero. -/
theorem integral_smul_ne_zero (a : Y → ℂ) (o : Y → E) (v : E) (hv : v ≠ 0)
    (hao : Integrable (fun y => a y • o y) μ) (ha : Integrable a μ)
    (ha1 : (∫ y, a y ∂μ) = 1) (hn : (∫ y, ‖a y‖ ∂μ) = 1)
    (hε : ∀ y, a y ≠ 0 → ‖o y - v‖ ≤ ‖v‖ / 2) :
    (∫ y, a y • o y ∂μ) ≠ 0 := by
  intro h0
  have h := norm_integral_smul_sub_le a o v hao ha ha1 hn hε
  rw [h0, zero_sub, norm_neg] at h
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  linarith

end Average

section Bump

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- A compactly supported continuous weight supported in a prescribed neighborhood, with
complex integral one and absolute integral one. -/
theorem exists_normalized_bump (y₀ : Y) {U : Set Y} (hU : U ∈ 𝓝 y₀) :
    ∃ a : C(Y, ℂ), HasCompactSupport a ∧ (∀ y, a y ≠ 0 → y ∈ U) ∧
      (∫ y, a y ∂μ) = 1 ∧ (∫ y, ‖a y‖ ∂μ) = 1 := by
  obtain ⟨W, hWU, hW, hyW⟩ := mem_nhds_iff.mp hU
  obtain ⟨f, hf₁, hfc, hfs, hfr⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hW
      (singleton_subset_iff.mpr hyW)
  have hfcs : HasCompactSupport f := hfc
  have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport hfcs
  have hfy : f y₀ ≠ 0 := by
    rw [hf₁ (mem_singleton y₀)]
    exact one_ne_zero
  have hfpos : 0 < ∫ y, f y ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero f.continuous hfi (fun y => (hfr y).1) hfy
  let a : C(Y, ℂ) := ⟨fun y => ((f y / (∫ z, f z ∂μ) : ℝ) : ℂ), by fun_prop⟩
  have hacs : HasCompactSupport a := by
    apply hfcs.mono
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro hfy0
    apply hy
    simp [a, hfy0]
  have ha : (∫ y, a y ∂μ) = 1 := by
    change (∫ y, ((f y / (∫ z, f z ∂μ) : ℝ) : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, integral_div, div_self hfpos.ne']
    rfl
  refine ⟨a, hacs, ?_, ha, ?_⟩
  · intro y hy
    apply hWU
    apply hfs
    apply subset_closure
    change f y ≠ 0
    intro hfy0
    exact hy (by simp [a, hfy0])
  · have hn (y : Y) : ‖a y‖ = f y / (∫ z, f z ∂μ) := by
      change ‖((f y / (∫ z, f z ∂μ) : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hfr y).1 hfpos.le)]
    simp_rw [hn]
    rw [integral_div, div_self hfpos.ne']

end Bump

section CompactRightInvariance

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- **Haar measure is right invariant under compact subgroups.** Right translation by an
element of a compact subgroup `K` multiplies a left Haar measure by a scalar, and this scalar is
one because right translation fixes the compact set `V K` of positive finite measure. -/
theorem map_mul_right_eq_self_of_isCompact (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  have hmap := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  let A : Set G := V * (K : Set G)
  have hAc : IsCompact A := hVc.mul hK
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hpre : (· * k) ⁻¹' A = A := by
    ext x
    simp only [mem_preimage, A]
    constructor
    · rintro ⟨v, hv, l, hl, hx⟩
      change v * l = x * k at hx
      refine ⟨v, hv, l * k⁻¹, K.mul_mem hl (K.inv_mem hk), ?_⟩
      change v * (l * k⁻¹) = x
      rw [← mul_assoc, hx, mul_inv_cancel_right]
    · rintro ⟨v, hv, l, hl, hx⟩
      change v * l = x at hx
      refine ⟨v, hv, l * k, K.mul_mem hl hk, ?_⟩
      change v * (l * k) = x * k
      rw [← mul_assoc, hx]
  have hApos : 0 < μ A := by
    apply Measure.measure_pos_of_mem_nhds (μ := μ) (x := 1)
    apply mem_of_superset hV1
    intro v hv
    exact ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hAfin : μ A ≠ ⊤ := hAc.measure_lt_top.ne
  have hval : μ A = (c : ENNReal) * μ A := by
    have h1 : Measure.map (· * k) μ A = μ A := by
      rw [Measure.map_apply (measurable_mul_const k) hAm, hpre]
    rw [hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact h1.symm
  have hc1 : (c : ENNReal) = 1 := by
    have h := (ENNReal.mul_eq_right hApos.ne' hAfin).mp hval.symm
    exact h
  rw [hmap, show c = 1 from by exact_mod_cast hc1, one_smul]

end CompactRightInvariance

end Langlands.Analysis.NormalizedAverage
