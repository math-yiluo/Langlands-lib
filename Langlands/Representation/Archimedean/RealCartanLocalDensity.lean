import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian

/-! # A local density for the compact Cartan trace -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Langlands.Archimedean.RealCartanLocalDensity

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In a smooth coordinate change near a point with invertible derivative,
the pushed-forward density is continuous at the image point. Its value is the
original density divided by the absolute determinant at that point. -/
def RealCartanLocalDensityStatement (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → E) (x : E) (D : E ≃L[ℝ] E)
    (w : E → ℂ) (U : Set E), IsOpen U → x ∈ U →
    ContDiffAt ℝ 1 f x → HasFDerivAt f (D : E →L[ℝ] E) x → ContinuousAt w x →
    ∃ (s t : Set E) (W : E → ℂ), IsOpen s ∧ x ∈ s ∧ s ⊆ U ∧
      IsOpen t ∧ f x ∈ t ∧ ContinuousAt W (f x) ∧
      W (f x) = |(D : E →L[ℝ] E).det|⁻¹ • w x ∧
      ∀ φ : E → ℂ, ∫ z in s, φ (f z) * w z ∂μ = ∫ y in t, φ y * W y ∂μ

theorem realCartanLocalDensity : RealCartanLocalDensityStatement E := by
  intro μ _ f x D w U hU hxU hf hD hw
  let e := hf.toOpenPartialHomeomorph f hD one_ne_zero
  have hx : x ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD one_ne_zero
  have hy : f x ∈ e.target := e.map_source hx
  have hinv : e.symm (f x) = x := e.left_inv hx
  have hinvcont := e.continuousAt_symm hy
  let J (z : E) := |(fderiv ℝ f z).det|
  have hJ : ContinuousAt J x :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      (hf.continuousAt_fderiv one_ne_zero)).abs
  have hJx : J x ≠ 0 := by
    change |(fderiv ℝ f x).det| ≠ 0
    rw [hD.fderiv]
    exact abs_ne_zero.mpr D.toLinearEquiv.isUnit_det'.ne_zero
  have hJnear : {z : E | J z ≠ 0} ∈ 𝓝 x := hJ.eventually (eventually_ne_nhds hJx)
  obtain ⟨v, hv, hvdiff⟩ := hf.contDiffOn (m := 1) le_rfl (by simp)
  have hnear : ((v ∩ e.source) ∩ U) ∩ {z : E | J z ≠ 0} ∈ 𝓝 x :=
    inter_mem (inter_mem (inter_mem hv (e.open_source.mem_nhds hx)) (hU.mem_nhds hxU)) hJnear
  obtain ⟨s, hsSub, hs, hxs⟩ := mem_nhds_iff.mp hnear
  have hsSource : s ⊆ e.source := fun z hz => (hsSub hz).1.1.2
  have hfd (z : E) (hz : z ∈ s) : HasFDerivAt f (fderiv ℝ f z) z :=
    (hvdiff.differentiableOn one_ne_zero z (hsSub hz).1.1.1).differentiableAt
      (Filter.mem_of_superset (hs.mem_nhds hz) fun _ hz' => (hsSub hz').1.1.1)
      |>.hasFDerivAt
  let W (y : E) := (J (e.symm y))⁻¹ • w (e.symm y)
  have hW : ContinuousAt W (f x) := by
    have hcont : ContinuousAt (fun z => (J z)⁻¹ • w z) (e.symm (f x)) := by
      rw [hinv]
      exact (hJ.inv₀ hJx).smul hw
    exact hcont.comp hinvcont
  refine ⟨s, f '' s, W, hs, hxs, fun z hz => (hsSub hz).1.2,
    e.isOpen_image_of_subset_source hs hsSource, mem_image_of_mem _ hxs, hW, ?_, ?_⟩
  · simp only [W, hinv, J, hD.fderiv]
  · intro φ
    have hchange := integral_image_eq_integral_abs_det_fderiv_smul μ hs.measurableSet
      (fun z hz => (hfd z hz).hasFDerivWithinAt) (e.injOn.mono hsSource)
      (fun y => φ y * W y)
    rw [hchange]
    refine setIntegral_congr_fun hs.measurableSet fun z hz => ?_
    have hsz : J z ≠ 0 := (hsSub hz).2
    have hinvz : e.symm (f z) = z := e.left_inv (hsSource hz)
    change φ (f z) * w z = J z •
      (φ (f z) * ((J (e.symm (f z)))⁻¹ • w (e.symm (f z))))
    rw [hinvz, mul_smul_comm, smul_smul, mul_inv_cancel₀ hsz, one_smul]

end Langlands.Archimedean.RealCartanLocalDensity
