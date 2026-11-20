import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Complementary slices of the real Fourier transform -/

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform NNReal RealInnerProductSpace SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u v

private theorem exists_schwartz_norm_majorant {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.HasTemperateGrowth]
    (Φ : 𝓢(V, ℂ)) : ∃ B : W → ℝ, Integrable B μ ∧
      ∀ z : V, ∀ x : W, ‖x‖ ≤ ‖z‖ → ‖Φ z‖ ≤ B x := by
  let l := μ.integrablePower
  let C₀ := SchwartzMap.seminorm ℝ 0 0 Φ
  let C₁ := SchwartzMap.seminorm ℝ l 0 Φ
  refine ⟨fun x => 2 ^ l * (C₀ + C₁) * (1 + ‖x‖) ^ (-(l : ℝ)),
    (μ.integrable_pow_neg_integrablePower).const_mul _, ?_⟩
  intro z x hx
  have hpow : ‖x‖ ^ (0 + l) * ‖Φ z‖ ≤ C₁ := by
    rw [zero_add]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (norm_nonneg _)).trans
      (Φ.norm_pow_mul_le_seminorm ℝ l z)
  simpa only [pow_zero, one_mul] using pow_mul_le_of_le_of_pow_mul_le
    (norm_nonneg x) (norm_nonneg (Φ z)) (Φ.norm_le_seminorm ℝ z) hpow

section Product

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

local notation "P" => WithLp 2 (E × F)

/-- The positive Fourier integral in the first factor at a fixed frequency. -/
def firstFactorFourier (Φ : 𝓢(P, ℂ)) (ξ : E) (y : F) : ℂ :=
  ∫ x : E, Real.fourierChar (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, y))

private theorem integrable_circle_twist (Φ : 𝓢(P, ℂ)) (χ : E × F → Circle)
    (hχ : Continuous χ) : Integrable (fun p => χ p • Φ (WithLp.toLp 2 p)) := by
  have hΦ : Integrable (fun p : E × F => Φ (WithLp.toLp 2 p)) :=
    (WithLp.volume_preserving_toLp E F).integrable_comp_of_integrable Φ.integrable
  have hCont := hχ.smul (Φ.continuous.comp (WithLp.prod_continuous_toLp 2 E F))
  apply hΦ.mono hCont.aestronglyMeasurable
  exact Eventually.of_forall (fun _ => by simp [Circle.smul_def])

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem continuous_firstFactorIntegrand (Φ : 𝓢(P, ℂ)) (ξ : E) (y : F) :
    Continuous (fun x : E => Real.fourierChar (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, y))) :=
  (Real.continuous_fourierChar.comp (continuous_id.inner (𝕜 := ℝ) continuous_const)).smul
    (Φ.continuous.comp ((WithLp.prod_continuous_toLp 2 E F).comp
      (continuous_id.prodMk continuous_const)))

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem continuous_firstFactorFourier (Φ : 𝓢(P, ℂ)) (ξ : E) :
    Continuous (firstFactorFourier Φ ξ) := by
  obtain ⟨B, hB, hbound⟩ := exists_schwartz_norm_majorant (volume : Measure E) Φ
  unfold firstFactorFourier
  apply continuous_of_dominated (bound := B)
  · intro y
    exact (continuous_firstFactorIntegrand Φ ξ y).aestronglyMeasurable
  · intro y
    apply Eventually.of_forall
    intro x
    simp only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
    exact hbound _ _ (WithLp.norm_fst_le (α := E) (β := F) (WithLp.toLp 2 (x, y)))
  · exact hB
  · apply Eventually.of_forall
    intro x
    exact continuous_const.smul
      (Φ.continuous.comp ((WithLp.prod_continuous_toLp 2 E F).comp
        (continuous_const.prodMk continuous_id)))

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem integrable_firstFactorIntegrand (Φ : 𝓢(P, ℂ)) (ξ : E) (y : F) :
    Integrable (fun x : E => Real.fourierChar (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, y))) := by
  obtain ⟨B, hB, hbound⟩ := exists_schwartz_norm_majorant (volume : Measure E) Φ
  apply hB.mono (continuous_firstFactorIntegrand Φ ξ y).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  simp only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  exact (hbound _ _ (WithLp.norm_fst_le (α := E) (β := F) (WithLp.toLp 2 (x, y)))).trans (le_abs_self _)

private theorem integrable_firstFactorFourier (Φ : 𝓢(P, ℂ)) (ξ : E) :
    Integrable (firstFactorFourier Φ ξ) := by
  have h := integrable_circle_twist Φ (fun p => Real.fourierChar (inner ℝ p.1 ξ))
    (Real.continuous_fourierChar.comp (continuous_fst.inner (𝕜 := ℝ) continuous_const))
  exact h.integral_prod_right

/-- Fubini writes the full positive transform as the positive transform of the
first-factor integral, at the same first frequency. -/
theorem fourierInv_firstFactorFourier (Φ : 𝓢(P, ℂ)) (ξ : E) (ζ : F) :
    𝓕⁻ (firstFactorFourier Φ ξ) ζ = (𝓕⁻ Φ : 𝓢(P, ℂ)) (WithLp.toLp 2 (ξ, ζ)) := by
  let χ : E × F → Circle := fun p => Real.fourierChar (inner ℝ p.1 ξ + inner ℝ p.2 ζ)
  have hχ : Continuous χ := Real.continuous_fourierChar.comp
    ((continuous_fst.inner (𝕜 := ℝ) (continuous_const (y := ξ))).add
      (continuous_snd.inner (𝕜 := ℝ) (continuous_const (y := ζ))))
  have hTwist := integrable_circle_twist Φ χ hχ
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq]
  symm
  calc
    _ = ∫ p : E × F, χ p • Φ (WithLp.toLp 2 p) := by
      simpa only [χ, WithLp.prod_inner_apply, MeasurableEquiv.toLp_apply, WithLp.ofLp_toLp] using
        ((WithLp.volume_preserving_toLp E F).integral_comp'
          (f := MeasurableEquiv.toLp 2 (E × F))
          (fun z : P => Real.fourierChar (inner ℝ z (WithLp.toLp 2 (ξ, ζ))) • Φ z)).symm
    _ = ∫ y : F, ∫ x : E, χ (x, y) • Φ (WithLp.toLp 2 (x, y)) := integral_prod_symm _ hTwist
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [firstFactorFourier, Circle.smul_def, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [χ, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring

private theorem integrable_fourierInv_slice (Φ : 𝓢(P, ℂ)) (ξ : E) :
    Integrable (fun y : F => (𝓕⁻ Φ : 𝓢(P, ℂ)) (WithLp.toLp 2 (ξ, y))) := by
  obtain ⟨B, hB, hbound⟩ := exists_schwartz_norm_majorant (volume : Measure F) (𝓕⁻ Φ)
  apply hB.mono
    (((𝓕⁻ Φ : 𝓢(P, ℂ)).continuous.comp ((WithLp.prod_continuous_toLp 2 E F).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro y
  exact (hbound _ _ (WithLp.norm_snd_le (α := E) (β := F) (WithLp.toLp 2 (ξ, y)))).trans (le_abs_self _)

end Product

/-- Complementary real affine slices for the positive Fourier transform and
its negative phase in the second integration. -/
def RealGodementProductFourierStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (Φ : 𝓢(WithLp 2 (E × F), ℂ)) (ξ : E) (η : F),
    Integrable (fun x : E => Real.fourierChar (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η))) ∧
    Integrable (fun y : F => Real.fourierChar (-(inner ℝ y η)) •
      (𝓕⁻ Φ : 𝓢(WithLp 2 (E × F), ℂ)) (WithLp.toLp 2 (ξ, y))) ∧
    (∫ y : F, Real.fourierChar (-(inner ℝ y η)) •
        (𝓕⁻ Φ : 𝓢(WithLp 2 (E × F), ℂ)) (WithLp.toLp 2 (ξ, y))) =
      ∫ x : E, Real.fourierChar (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η))

theorem realGodementProductFourier : RealGodementProductFourierStatement.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ Φ ξ η
  have hEq := funext (fourierInv_firstFactorFourier Φ ξ)
  have hI : Integrable (𝓕⁻ (firstFactorFourier Φ ξ)) :=
    hEq.symm ▸ integrable_fourierInv_slice Φ ξ
  refine ⟨integrable_firstFactorIntegrand Φ ξ η,
    (Real.fourierIntegral_convergent_iff η).mpr (integrable_fourierInv_slice Φ ξ), ?_⟩
  have hNeg : Integrable (𝓕 (firstFactorFourier Φ ξ)) := by
    have h := (LinearIsometryEquiv.neg ℝ (E := F)).measurePreserving.integrable_comp_of_integrable hI
    convert h using 1
    funext y
    simp [Function.comp_apply, Real.fourierInv_eq_fourier_neg]
  have hInv := (integrable_firstFactorFourier Φ ξ).fourier_fourierInv_eq hNeg
    (continuous_firstFactorFourier Φ ξ).continuousAt (v := η)
  rwa [hEq, Real.fourier_eq, firstFactorFourier] at hInv

end Langlands.Global.RankinSelbergGlobal.RealGodement
