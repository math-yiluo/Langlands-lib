import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolution

/-! # Combining independently scaled determinant reflections -/

noncomputable section

open MeasureTheory

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

open ArchimedeanMellinConvolution (mconv measurable_mconv rapidDecay_mconv mellin_mconv theta_mconv scale)

/-- Multiplicative convolution of two profiles, using one logarithmic variable. -/
def mellinConvolution (f g : ℝ → ℂ) : ℝ → ℂ := mconv (m := 1) 1 f (fun _ => g)

/-- The two-factor form of the published Mellin convolution theorem. -/
theorem archimedeanBinaryMellinConvolution (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : RapidDecay f) (hg : RapidDecay g) :
    Measurable (mellinConvolution f g) ∧ RapidDecay (mellinConvolution f g) ∧
      ∀ s : ℂ, mellin (mellinConvolution f g) s = mellin f s * mellin g s := by
  refine ⟨measurable_mconv 1 hfm (fun _ : Fin 1 => hgm),
    rapidDecay_mconv one_ne_zero hf (fun _ : Fin 1 => hgm) (fun _ => hg), fun s => ?_⟩
  simpa only [mellinConvolution, Fin.prod_univ_one] using
    mellin_mconv hfm (fun _ : Fin 1 => hgm) hf (fun _ => hg) s

/-- A weighted integral with independent positive scales in the two determinant variables. -/
def separatedTheta {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℂ)
    (δ η : X → ℝ) (f g : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ x, F x * (f (a * δ x) * g (b * η x)) ∂μ

/-- The product-determinant theta integral is the log-scale average of the separated integrals. -/
theorem theta_mellinConvolution_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {F : X → ℂ} {δ η : X → ℝ} {f g : ℝ → ℂ} (hF : AEStronglyMeasurable F μ)
    (hδ : Measurable δ) (hη : Measurable η) (hδ₀ : ∀ x, 0 < δ x) (hη₀ : ∀ x, 0 < η x)
    (hf : RapidDecay f) (hg : RapidDecay g) (hfm : Measurable f) (hgm : Measurable g)
    {σ : ℝ} (hI : Integrable (fun x => ‖F x‖ * (δ x * η x) ^ σ) μ) {b : ℝ} (hb : 0 < b) :
    theta μ F (fun x => δ x * η x) (mellinConvolution f g) b =
      ∫ u : ℝ, separatedTheta μ F δ η f g (b * Real.exp u) (Real.exp (-u)) := by
  let D : Fin 2 → X → ℝ := ![δ, η]
  let W : Fin 2 → ℝ → ℂ := ![f, g]
  have hDm (i : Fin 2) : Measurable (D i) := by fin_cases i <;> assumption
  have hD (i : Fin 2) (x : X) : 0 < D i x := by fin_cases i <;> solve_by_elim
  have hWm (i : Fin 2) : Measurable (W i) := by fin_cases i <;> assumption
  have hW (i : Fin 2) : RapidDecay (W i) := by fin_cases i <;> assumption
  have hprod (x : X) : (∏ i, D i x) = δ x * η x := by simp [D, Fin.prod_univ_two]
  have hMom : Integrable (fun x => ‖F x‖ * (∏ i, D i x) ^ σ) μ := by
    simpa only [hprod] using hI
  have hTheta := theta_mconv μ hF hDm hD hWm hW hMom (ε := 1) one_ne_zero hb
  have hFirst : W 0 = f := rfl
  have hRest (j : Fin 1) : W j.succ = g := by fin_cases j; rfl
  have hScale (τ : Fin 1 → ℝ) : scale 1 b τ 1 = Real.exp (τ 0) := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, ArchimedeanMellinConvolution.scale_succ, one_mul]
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he : MeasurePreserving e (volume : Measure (Fin 1 → ℝ)) volume := by
    rw [volume_pi]
    exact measurePreserving_piUnique (fun _ : Fin 1 => (volume : Measure ℝ))
  let A (u : ℝ) := separatedTheta μ F δ η f g (b * Real.exp (-u)) (Real.exp u)
  calc
    _ = ∫ τ : Fin 1 → ℝ, ∫ x, F x * ∏ i, W i (scale 1 b τ i * D i x) ∂μ := by
      simpa only [hprod, hFirst, hRest, mellinConvolution] using hTheta
    _ = ∫ τ : Fin 1 → ℝ, A (e τ) := by
      simp only [A, separatedTheta, Fin.prod_univ_two, D, W, Matrix.cons_val_zero, Matrix.cons_val_one,
        ArchimedeanMellinConvolution.scale_zero, hScale,
        Fin.sum_univ_one, one_mul]
      rfl
    _ = ∫ u : ℝ, A u := he.integral_comp e.measurableEmbedding A
    _ = _ := by rw [← integral_neg_eq_self A volume]; simp only [A, neg_neg]

/-- The separated reflection at all positive scales yields the theta identity for the convolution weights. -/
def ArchimedeanMellinConvolutionReflectionStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ η : X → ℝ) (δd ηd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν →
    Measurable δ → Measurable η → Measurable δd → Measurable ηd →
    (∀ x, 0 < δ x) → (∀ x, 0 < η x) → (∀ y, 0 < δd y) → (∀ y, 0 < ηd y) →
    ∀ {σ : ℝ}, Integrable (fun x => ‖F x‖ * (δ x * η x) ^ σ) μ →
    Integrable (fun y => ‖Fd y‖ * (δd y * ηd y) ^ σ) ν →
    ∀ (f g fd gd : ℝ → ℂ), Measurable f → Measurable g → Measurable fd → Measurable gd →
    RapidDecay f → RapidDecay g → RapidDecay fd → RapidDecay gd →
    (∀ a b : ℝ, 0 < a → 0 < b → separatedTheta μ F δ η f g a b =
      ((a * b : ℝ) : ℂ) * separatedTheta ν Fd δd ηd fd gd a⁻¹ b⁻¹) →
    ∀ {b : ℝ}, 0 < b → theta μ F (fun x => δ x * η x) (mellinConvolution f g) b =
      (b : ℂ) * theta ν Fd (fun y => δd y * ηd y) (mellinConvolution fd gd) b⁻¹

theorem archimedeanMellinConvolutionReflection : ArchimedeanMellinConvolutionReflectionStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ η δd ηd hF hFd hδ hη hδd hηd hδ₀ hη₀ hδd₀ hηd₀ σ hI hId
    f g fd gd hfm hgm hfdm hgdm hf hg hfd hgd hEq b hb
  rw [theta_mellinConvolution_eq μ hF hδ hη hδ₀ hη₀ hf hg hfm hgm hI hb,
    theta_mellinConvolution_eq ν hFd hδd hηd hδd₀ hηd₀ hfd hgd hfdm hgdm hId (inv_pos.mpr hb), ← integral_const_mul]
  let A (u : ℝ) := (b : ℂ) * separatedTheta ν Fd δd ηd fd gd (b⁻¹ * Real.exp u) (Real.exp (-u))
  change (∫ u : ℝ, separatedTheta μ F δ η f g (b * Real.exp u) (Real.exp (-u))) = ∫ u : ℝ, A u
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp measurableEmbedding_neg A]
  apply integral_congr_ae
  refine ae_of_all _ fun u => ?_
  change separatedTheta μ F δ η f g (b * Real.exp u) (Real.exp (-u)) = A (-u)
  rw [hEq _ _ (mul_pos hb (Real.exp_pos _)) (Real.exp_pos _)]
  rw [show b * Real.exp u * Real.exp (-u) = b by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]]
  simp only [A, mul_inv_rev, ← Real.exp_neg, neg_neg, mul_comm (Real.exp (-u)) b⁻¹]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair
