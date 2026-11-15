import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Integration by parts on `ℂ` for the rank-one Jacquet functional

Identities for integrals over `ℂ` (Lebesgue measure) of directional derivatives of a
`C¹` function `φ : ℂ → ℂ`:

* `integral_fderiv_one_eq_zero`, `integral_fderiv_I_eq_zero`: `∫ Dφ(z) 1 = 0` and
  `∫ Dφ(z) i = 0` when the derivative is integrable and `φ` tends to `0` at infinity;
* `integral_fderiv_apply_self`: `∫ Dφ(z) z = -2 ∫ φ` (Euler's identity, from the scaling
  `∫ φ(r z) dz = r⁻² ∫ φ`);
* `integral_fderiv_apply_I_mul_self`: `∫ Dφ(z) (i z) = 0` (from rotation invariance).

The hypotheses are bounds by multiples of `(1 + |z|)⁻³`, which is integrable on `ℂ`.
-/

noncomputable section

open MeasureTheory Filter Topology Module Set

namespace Langlands.Archimedean.ComplexSwapJacquet

/-! ## The majorant `(1 + |z|)⁻³` -/

theorem integrable_inv_one_add_norm_pow_three :
    Integrable (fun z : ℂ => ((1 + ‖z‖) ^ 3)⁻¹) := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine h.congr (Eventually.of_forall fun z => ?_)
  have hz : 0 ≤ 1 + ‖z‖ := by positivity
  simp only
  rw [Real.rpow_neg hz]
  norm_cast

theorem nonneg_of_bound {φ : ℂ → ℂ} {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹) :
    0 ≤ C := by
  have h := hb 0
  simp only [norm_zero, add_zero, one_pow, inv_one, mul_one] at h
  exact (norm_nonneg _).trans h

theorem integrable_of_bound {φ : ℂ → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹) : Integrable φ :=
  (integrable_inv_one_add_norm_pow_three.const_mul C).mono' hφ.aestronglyMeasurable
    (Eventually.of_forall hb)

/-- A function bounded by `C (1 + |z|)⁻¹` tends to `0` at infinity. -/
theorem tendsto_cobounded_of_bound {φ : ℂ → ℂ} {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C * (1 + ‖z‖)⁻¹) :
    Tendsto φ (Bornology.cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun z : ℂ => (1 + ‖z‖)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    (tendsto_atTop_add_const_left _ 1 tendsto_norm_cobounded_atTop).inv_tendsto_atTop
  have h2 := h1.const_mul C
  rw [mul_zero] at h2
  exact squeeze_zero_norm hb h2

/-! ## Integrals of derivatives along the coordinate directions -/

theorem tendsto_line_re_atTop (y : ℝ) :
    Tendsto (fun x : ℝ => (⟨x, y⟩ : ℂ)) atTop (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun x => ?_) tendsto_abs_atTop_atTop
  simpa using Complex.abs_re_le_norm (⟨x, y⟩ : ℂ)

theorem tendsto_line_re_atBot (y : ℝ) :
    Tendsto (fun x : ℝ => (⟨x, y⟩ : ℂ)) atBot (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun x => ?_) tendsto_abs_atBot_atTop
  simpa using Complex.abs_re_le_norm (⟨x, y⟩ : ℂ)

theorem tendsto_line_im_atTop (x : ℝ) :
    Tendsto (fun y : ℝ => (⟨x, y⟩ : ℂ)) atTop (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun y => ?_) tendsto_abs_atTop_atTop
  simpa using Complex.abs_im_le_norm (⟨x, y⟩ : ℂ)

theorem tendsto_line_im_atBot (x : ℝ) :
    Tendsto (fun y : ℝ => (⟨x, y⟩ : ℂ)) atBot (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono (fun y => ?_) tendsto_abs_atBot_atTop
  simpa using Complex.abs_im_le_norm (⟨x, y⟩ : ℂ)

theorem hasDerivAt_line_re (y x : ℝ) : HasDerivAt (fun x : ℝ => (⟨x, y⟩ : ℂ)) 1 x := by
  have h : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  rw [h]
  simpa using (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * Complex.I)

theorem hasDerivAt_line_im (x y : ℝ) :
    HasDerivAt (fun y : ℝ => (⟨x, y⟩ : ℂ)) Complex.I y := by
  have h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp
  rw [h]
  simpa using ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)

/-- `∫ Dφ(z) 1 dz = 0` for a `C¹` function tending to `0` at infinity with integrable
derivative along `1`. -/
theorem integral_fderiv_one_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hint : Integrable fun z => fderiv ℝ φ z 1)
    (hlim : Tendsto φ (Bornology.cobounded ℂ) (𝓝 0)) :
    ∫ z, fderiv ℝ φ z 1 = 0 := by
  set g : ℂ → ℂ := fun z => fderiv ℝ φ z 1 with hg
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hmp.integral_comp hemb g]
  have hint2 : Integrable (fun p : ℝ × ℝ => g (Complex.measurableEquivRealProd.symm p))
      (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).mpr hint
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod_symm _ hint2]
  apply integral_eq_zero_of_ae
  filter_upwards [hint2.prod_left_ae] with y hy
  simp only [Complex.measurableEquivRealProd_symm_apply, Pi.zero_apply] at hy ⊢
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => φ ⟨x, y⟩) (g ⟨x, y⟩) x := by
    intro x
    have h := ((hφ.differentiable one_ne_zero) ⟨x, y⟩).hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_line_re y x)
    exact h
  rw [integral_of_hasDerivAt_of_tendsto hd hy (hlim.comp (tendsto_line_re_atBot y))
    (hlim.comp (tendsto_line_re_atTop y)), sub_zero]

/-- `∫ Dφ(z) i dz = 0` for a `C¹` function tending to `0` at infinity with integrable
derivative along `i`. -/
theorem integral_fderiv_I_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hint : Integrable fun z => fderiv ℝ φ z Complex.I)
    (hlim : Tendsto φ (Bornology.cobounded ℂ) (𝓝 0)) :
    ∫ z, fderiv ℝ φ z Complex.I = 0 := by
  set g : ℂ → ℂ := fun z => fderiv ℝ φ z Complex.I with hg
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hmp.integral_comp hemb g]
  have hint2 : Integrable (fun p : ℝ × ℝ => g (Complex.measurableEquivRealProd.symm p))
      (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).mpr hint
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod _ hint2]
  apply integral_eq_zero_of_ae
  filter_upwards [hint2.prod_right_ae] with x hx
  simp only [Complex.measurableEquivRealProd_symm_apply, Pi.zero_apply] at hx ⊢
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => φ ⟨x, y⟩) (g ⟨x, y⟩) y := by
    intro y
    have h := ((hφ.differentiable one_ne_zero) ⟨x, y⟩).hasFDerivAt.comp_hasDerivAt y
      (hasDerivAt_line_im x y)
    exact h
  rw [integral_of_hasDerivAt_of_tendsto hd hx (hlim.comp (tendsto_line_im_atBot x))
    (hlim.comp (tendsto_line_im_atTop x)), sub_zero]

/-! ## Scaling and rotation -/

theorem inv_one_add_mul_pow_three_le {r : ℝ} (hr : 1 / 2 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    ((1 + r * x) ^ 3)⁻¹ ≤ 8 * ((1 + x) ^ 3)⁻¹ := by
  have h8 : (2 * (1 + r * x)) ^ 3 = 8 * (1 + r * x) ^ 3 := by ring
  have hpos : 0 < 1 + x := by linarith
  calc ((1 + r * x) ^ 3)⁻¹ = 8 * ((2 * (1 + r * x)) ^ 3)⁻¹ := by
        rw [h8, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (8 : ℝ) ≠ 0), one_mul]
    _ ≤ 8 * ((1 + x) ^ 3)⁻¹ := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.2 hr) hx]

/-- Euler's identity `∫ Dφ(z) z dz = -2 ∫ φ`, from `∫ φ(r z) dz = r⁻² ∫ φ`. -/
theorem integral_fderiv_apply_self {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {C : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹)
    (hb' : ∀ z, ‖fderiv ℝ φ z z‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹) :
    ∫ z, fderiv ℝ φ z z = -2 * ∫ z, φ z := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hC : 0 ≤ C := nonneg_of_bound hb
  have hs : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hbound : ∀ z : ℂ, ∀ r ∈ Metric.ball (1 : ℝ) (1 / 2),
      ‖fderiv ℝ φ (r • z) z‖ ≤ 16 * C * ((1 + ‖z‖) ^ 3)⁻¹ := by
    intro z r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    have hr1 : 1 / 2 ≤ r := by linarith
    have hr0 : 0 < r := by linarith
    have heq : fderiv ℝ φ (r • z) z = r⁻¹ • fderiv ℝ φ (r • z) (r • z) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    have h1 := hb' (r • z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at h1
    have h2 := inv_one_add_mul_pow_three_le hr1 (norm_nonneg z)
    have hr2 : r⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
    calc r⁻¹ * ‖fderiv ℝ φ (r • z) (r • z)‖ ≤ 2 * (C * ((1 + r * ‖z‖) ^ 3)⁻¹) :=
          mul_le_mul hr2 h1 (norm_nonneg _) (by norm_num)
      _ ≤ 2 * (C * (8 * ((1 + ‖z‖) ^ 3)⁻¹)) := by gcongr
      _ = 16 * C * ((1 + ‖z‖) ^ 3)⁻¹ := by ring
  have hderiv : ∀ z : ℂ, ∀ r ∈ Metric.ball (1 : ℝ) (1 / 2),
      HasDerivAt (fun r : ℝ => φ (r • z)) (fderiv ℝ φ (r • z) z) r := by
    intro z r _
    have h := (hd (r • z)).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).smul_const z)
    rw [one_smul] at h
    exact h
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (r : ℝ) (z : ℂ) => φ (r • z))
    (F' := fun (r : ℝ) (z : ℂ) => fderiv ℝ φ (r • z) z)
    (bound := fun z => 16 * C * ((1 + ‖z‖) ^ 3)⁻¹) hs
    (Eventually.of_forall fun r =>
      (hφ.continuous.comp (continuous_const_smul r)).aestronglyMeasurable)
    (by simpa using integrable_of_bound hφ.continuous hb)
    (((hfc.comp (continuous_const_smul (1 : ℝ))).clm_apply continuous_id).aestronglyMeasurable)
    (Eventually.of_forall hbound)
    (integrable_inv_one_add_norm_pow_three.const_mul (16 * C))
    (Eventually.of_forall hderiv)
  have hscale : (fun r : ℝ => ∫ z, φ (r • z)) =ᶠ[𝓝 (1 : ℝ)]
      fun r : ℝ => ((r ^ 2)⁻¹ : ℝ) • ∫ z, φ z := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with r hr
    rw [Measure.integral_comp_smul_of_nonneg volume φ r (hR := le_of_lt hr),
      Complex.finrank_real_complex]
  have hder2 : HasDerivAt (fun r : ℝ => ((r ^ 2)⁻¹ : ℝ) • ∫ z, φ z)
      ((-2 : ℝ) • ∫ z, φ z) 1 := by
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).inv (by norm_num)).smul_const (∫ z, φ z)
    convert h using 2
    norm_num
  have huniq := hmain.2.unique (hder2.congr_of_eventuallyEq hscale)
  simp only [one_smul] at huniq
  rw [huniq, Complex.real_smul]
  push_cast
  ring

/-- `∫ Dφ(z) (i z) dz = 0`, from the rotation invariance `∫ φ(e^{iθ} z) dz = ∫ φ`. -/
theorem integral_fderiv_apply_I_mul_self {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {C : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹)
    (hb' : ∀ z, ‖fderiv ℝ φ z (Complex.I * z)‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹) :
    ∫ z, fderiv ℝ φ z (Complex.I * z) = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hnorm : ∀ (θ : ℝ) (z : ℂ), ‖Complex.exp (θ * Complex.I) * z‖ = ‖z‖ := by
    intro θ z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hbound : ∀ z : ℂ, ∀ θ ∈ (Set.univ : Set ℝ),
      ‖fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
        (Complex.I * (Complex.exp (θ * Complex.I) * z))‖ ≤ C * ((1 + ‖z‖) ^ 3)⁻¹ := by
    intro z θ _
    have h := hb' (Complex.exp (θ * Complex.I) * z)
    rwa [hnorm] at h
  have hderiv : ∀ z : ℂ, ∀ θ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun θ : ℝ => φ (Complex.exp (θ * Complex.I) * z))
        (fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
          (Complex.I * (Complex.exp (θ * Complex.I) * z))) θ := by
    intro z θ _
    have hγ : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) * z)
        (Complex.I * (Complex.exp (θ * Complex.I) * z)) θ := by
      have h := (((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).cexp).mul_const z
      refine h.congr_deriv ?_
      simp only [id_eq]
      push_cast
      ring
    exact (hd _).hasFDerivAt.comp_hasDerivAt θ hγ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (x₀ := (0 : ℝ))
    (F := fun (θ : ℝ) (z : ℂ) => φ (Complex.exp (θ * Complex.I) * z))
    (F' := fun (θ : ℝ) (z : ℂ) => fderiv ℝ φ (Complex.exp (θ * Complex.I) * z)
      (Complex.I * (Complex.exp (θ * Complex.I) * z)))
    (bound := fun z => C * ((1 + ‖z‖) ^ 3)⁻¹) Filter.univ_mem
    (Eventually.of_forall fun θ =>
      (hφ.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (by simpa using integrable_of_bound hφ.continuous hb)
    (((hfc.comp (continuous_const.mul continuous_id)).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall hbound)
    (integrable_inv_one_add_norm_pow_three.const_mul C)
    (Eventually.of_forall hderiv)
  have hrot : (fun θ : ℝ => ∫ z, φ (Complex.exp (θ * Complex.I) * z)) =
      fun _ => ∫ z, φ z := by
    funext θ
    have hmp := (rotation (Circle.exp θ)).measurePreserving
    have hme := (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding
    have h := hmp.integral_comp hme φ
    simpa [rotation_apply, Circle.coe_exp] using h
  have huniq := hmain.2.unique (by rw [hrot]; exact hasDerivAt_const _ _)
  simpa using huniq

end Langlands.Archimedean.ComplexSwapJacquet
