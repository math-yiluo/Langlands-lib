import Langlands.Representation.Archimedean.RealSmallOrthogonalHaar
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Angular Haar measure near the identity of a small orthogonal group -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.Operator ENNReal

namespace Langlands.Archimedean.RealCartanAngularHaar

open RealSmallOrthogonalHaar RealBlockRotation

set_option autoImplicit false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

local instance orthogonalPseudoMetrizable (n : ℕ) : TopologicalSpace.PseudoMetrizableSpace (K n) := by
  have : TopologicalSpace.PseudoMetrizableSpace (M n) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin n → Fin n → ℝ)
    infer_instance
  exact Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

/-- The determinant-one component of the real compact factor. -/
def positiveComponent (n : ℕ) : Set (K n) := {k | k.val.det = 1}

theorem det_eq_one_or_neg_one {n : ℕ} (k : K n) : k.val.det = 1 ∨ k.val.det = -1 := by
  apply mul_self_eq_one_iff.mp
  have hk := (mem_orthogonalGroup_iff (Fin n) ℝ).mp k.2
  simpa only [det_mul, det_transpose, det_one] using congrArg Matrix.det hk

theorem isClopen_positiveComponent (n : ℕ) : IsClopen (positiveComponent n) := by
  have hc : Continuous (fun k : K n => k.val.det) := continuous_subtype_val.matrix_det
  have he : (positiveComponent n)ᶜ = (fun k : K n => k.val.det) ⁻¹' {-1} := by
    ext k
    rcases det_eq_one_or_neg_one k with h | h <;> norm_num [positiveComponent, h]
  exact ⟨isClosed_singleton.preimage hc, isClosed_compl_iff.mp (he ▸ isClosed_singleton.preimage hc)⟩

@[simp]
theorem one_mem_positiveComponent (n : ℕ) : (1 : K n) ∈ positiveComponent n := by
  simp [positiveComponent]

@[simp]
theorem det_rotation (θ : ℝ) : (rotation θ : M 2).det = 1 := by
  rw [rotation_val, det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_eq_one_iff {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
    rotation θ = 1 ↔ θ = 0 := by
  constructor
  · intro h
    have he : Real.cos θ = 1 := by
      have := congrArg (fun k : K 2 => k.val 0 0) h
      simpa [rotation_val] using this
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])).mp he
  · rintro rfl
    apply Subtype.ext
    rw [rotation_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem det_signReflection {n : ℕ} (i : Fin n) :
    (signReflection n i : M n).det = -1 := by
  rw [signReflection_val, det_diagonal, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem ext_of_complex {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [HasOuterApproxClosed α] {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (he : ∀ f : C(α, ℂ), (∫ a, f a ∂μ) = ∫ a, f a ∂ν) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have h := he ⟨fun a => (f a : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  simp only [ContinuousMap.coe_mk, integral_complex_ofReal, Complex.ofReal_inj] at h
  exact h

/-- The identity component of the orthogonal line has Haar mass one half. -/
theorem restrict_positive_one (μ : Measure (K 1)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ.restrict (positiveComponent 1) = ENNReal.ofReal (2⁻¹ : ℝ) • Measure.dirac 1 := by
  let s := positiveComponent 1
  have : IsFiniteMeasure (ENNReal.ofReal (2⁻¹ : ℝ) • Measure.dirac (1 : K 1)) :=
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply ext_of_complex
  intro f
  let F : C(K 1, ℂ) := ⟨s.indicator f, (isClopen_positiveComponent 1).continuous_indicator f.continuous⟩
  have ho : (1 : K 1) ∈ s := one_mem_positiveComponent 1
  have hn : signOne ∉ s := by
    change (signOne : M 1).det ≠ 1
    rw [det_signReflection]
    norm_num
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), integral_dirac]
  calc
    _ = ∫ k, F k ∂μ := (integral_indicator (isClopen_positiveComponent 1).1.measurableSet).symm
    _ = _ := by
      rw [integral_orthogonal_one]
      simp only [F, ContinuousMap.coe_mk, indicator_of_mem ho,
        indicator_of_notMem hn, add_zero, Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_ofNat]
      rw [div_eq_mul_inv, mul_comm]

/-- The full angular interval, with the origin in its interior. -/
abbrev angleInterval : Set ℝ := Icc (-Real.pi) Real.pi

/-- In rank two the determinant-one Haar component is angular Lebesgue measure
with density `1 / (4π)`. -/
theorem restrict_positive_two (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ.restrict (positiveComponent 2) = ENNReal.ofReal ((4 * Real.pi)⁻¹) •
      (volume.restrict angleInterval).map rotation := by
  let s := positiveComponent 2
  let ν : Measure ℝ := volume.restrict angleInterval
  have : IsFiniteMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top⟩
  have : IsFiniteMeasure (ENNReal.ofReal ((4 * Real.pi)⁻¹) • ν.map rotation) :=
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply ext_of_complex
  intro f
  let F : C(K 2, ℂ) := ⟨s.indicator f, (isClopen_positiveComponent 2).continuous_indicator f.continuous⟩
  have hp (θ : ℝ) : F (rotation θ) = f (rotation θ) := by
    have h : rotation θ ∈ s := det_rotation θ
    exact indicator_of_mem h _
  have hn (θ : ℝ) : F (rotation θ * reflectTwo) = 0 := by
    apply indicator_of_notMem
    change ((rotation θ : M 2) * (reflectTwo : M 2)).det ≠ 1
    rw [det_mul, det_rotation, det_signReflection]
    norm_num
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_map continuous_rotation.aemeasurable f.continuous.aestronglyMeasurable]
  have hperiodic : Function.Periodic (fun θ => f (rotation θ)) (2 * Real.pi) :=
    fun θ => congrArg f (rotation_periodic θ)
  have hlimits : (∫ θ in -Real.pi..Real.pi, f (rotation θ)) =
      ∫ θ in 0..2 * Real.pi, f (rotation θ) := by
    simpa only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      hperiodic.intervalIntegral_add_eq (-Real.pi) 0
  calc
    _ = ∫ k, F k ∂μ := (integral_indicator (isClopen_positiveComponent 2).1.measurableSet).symm
    _ = _ := by
      rw [integral_orthogonal_two]
      simp_rw [hp, hn, intervalIntegral.integral_zero, add_zero, ← hlimits,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
        restrict_Ioc_eq_restrict_Icc, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
        Complex.ofReal_ofNat, div_eq_mul_inv, mul_comm]

/-- The local angular measure formulas in ranks one and two. -/
def RealCartanAngularHaarStatement : Prop :=
  (∀ (μ : Measure (K 1)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ],
    μ.restrict (positiveComponent 1) = ENNReal.ofReal (2⁻¹ : ℝ) • Measure.dirac 1) ∧
  (∀ (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ],
    μ.restrict (positiveComponent 2) = ENNReal.ofReal ((4 * Real.pi)⁻¹) •
      (volume.restrict angleInterval).map rotation)

theorem realCartanAngularHaar : RealCartanAngularHaarStatement :=
  ⟨restrict_positive_one, restrict_positive_two⟩

end Langlands.Archimedean.RealCartanAngularHaar
