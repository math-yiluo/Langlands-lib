import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity

/-! # Weighted reflection by Mellin inversion and a contour shift -/

noncomputable section

open MeasureTheory Complex
open scoped Real

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

open ArchimedeanMellinPair (theta)
open ArchimedeanRealPairIdentity (ofReal_cpow_eq_exp)

private theorem ofReal_mul_cpow_pos {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (s : ℂ) :
    ((b * d : ℝ) : ℂ) ^ s = (b : ℂ) ^ s * (d : ℂ) ^ s := by
  rw [ofReal_cpow_eq_exp (mul_pos hb hd), ofReal_cpow_eq_exp hb, ofReal_cpow_eq_exp hd,
    Real.log_mul hb.ne' hd.ne', ofReal_add, add_mul, Complex.exp_add]

/-- A determinant-weighted integral on a line of absolute convergence factors into a vertical integral. -/
theorem theta_mellinInv_line {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {F : X → ℂ} {δ : X → ℝ} (hF : AEStronglyMeasurable F μ) (hδ : Measurable δ) (hpos : ∀ x, 0 < δ x)
    {m : ℂ → ℂ} (hm : Differentiable ℂ m) (hdec : StripDecay m)
    (σ : ℝ) (hInt : Integrable (fun x => ‖F x‖ * δ x ^ σ) μ) {b : ℝ} (hb : 0 < b) :
    theta μ F δ (mellinInv 0 m) b = (1 / (2 * π) : ℝ) • ∫ y : ℝ,
      (b : ℂ) ^ (-(((-σ : ℝ) : ℂ) + y * I)) *
        (∫ x, F x * (δ x : ℂ) ^ (-(((-σ : ℝ) : ℂ) + y * I)) ∂μ) * m (((-σ : ℝ) : ℂ) + y * I) := by
  let c : ℝ := 1 / (2 * π)
  let z (y : ℝ) : ℂ := ((-σ : ℝ) : ℂ) + y * I
  let A (p : X × ℝ) := F p.1 * (((b * δ p.1 : ℝ) : ℂ) ^ (-z p.2) * m (z p.2))
  have hz : Measurable z := measurable_const.add (measurable_ofReal.mul_const I)
  have hA : AEStronglyMeasurable A (μ.prod volume) := by
    have ht : Measurable (fun p : X × ℝ => ((b * δ p.1 : ℝ) : ℂ)) :=
      measurable_ofReal.comp ((hδ.comp measurable_fst).const_mul b)
    exact hF.comp_fst.mul ((ht.pow (hz.comp measurable_snd).neg).mul
      (hm.continuous.measurable.comp (hz.comp measurable_snd))).aestronglyMeasurable
  have hIm : Integrable (fun y : ℝ => m (z y)) := by
    obtain ⟨C, hC⟩ := hdec (-σ) (-σ)
    exact integrable_vertical hm.continuous (hC (-σ) le_rfl le_rfl)
  have hAi : Integrable A (μ.prod volume) := by
    refine (hInt.mul_prod (hIm.norm.const_mul (b ^ σ))).mono' hA (ae_of_all _ fun p => ?_)
    dsimp only [A, z]
    rw [norm_mul, norm_mul, norm_ofReal_cpow_neg (mul_pos hb (hpos p.1)), neg_neg,
      Real.mul_rpow hb.le (hpos p.1).le]
    ring_nf
    exact le_rfl
  calc
    theta μ F δ (mellinInv 0 m) b = c • ∫ x, (∫ y : ℝ, A (x, y)) ∂μ := by
      rw [theta, ← integral_smul]
      apply integral_congr_ae
      refine ae_of_all _ fun x => ?_
      change F x * mellinInv 0 m (b * δ x) = c • ∫ y : ℝ, A (x, y)
      rw [mellinInv_eq_of_stripDecay hm hdec (mul_pos hb (hpos x)) 0 (-σ)]
      simp only [mellinInv, z, A, c, smul_eq_mul, integral_const_mul, Complex.real_smul]
      ring
    _ = c • ∫ y, ∫ x, A (x, y) ∂μ := by
      rw [integral_integral_swap hAi]
    _ = _ := by
      apply congrArg (c • ·)
      apply integral_congr_ae
      refine ae_of_all _ fun y => ?_
      change (∫ x, A (x, y) ∂μ) =
        (b : ℂ) ^ (-z y) * (∫ x, F x * (δ x : ℂ) ^ (-z y) ∂μ) * m (z y)
      calc
        (∫ x, A (x, y) ∂μ) = ∫ x, ((b : ℂ) ^ (-z y) * m (z y)) * (F x * (δ x : ℂ) ^ (-z y)) ∂μ := by
          apply integral_congr_ae
          refine ae_of_all _ fun x => ?_
          simp only [A, ofReal_mul_cpow_pos hb (hpos x)]
          ring
        _ = _ := by rw [integral_const_mul]; ring

private theorem integral_comp_neg_real (f : ℝ → ℂ) : (∫ y, f (-y)) = ∫ y, f y :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp measurableEmbedding_neg f

private theorem cpow_reflection_scale {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (b : ℂ) * ((b⁻¹ : ℝ) : ℂ) ^ (-z) = (b : ℂ) ^ (1 + z) := by
  have he : (b : ℂ) = Complex.exp (Real.log b : ℂ) := by rw [← ofReal_exp, Real.exp_log hb]
  rw [ofReal_cpow_eq_exp (inv_pos.mpr hb), ofReal_cpow_eq_exp hb, Real.log_inv]
  conv_lhs => rw [he, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Compare the weighted ordinary and reflected kernels by shifting the common entire vertical integrand. -/
def ArchimedeanMellinWeightedReflectionStatement : Prop :=
  ∀ {X : Type u} {X' : Type v} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    {F : X → ℂ} {δ : X → ℝ} {Fd : X' → ℂ} {δd : X' → ℝ},
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd μ' → Measurable δ → Measurable δd →
    (∀ x, 0 < δ x) → (∀ x, 0 < δd x) →
    ∀ {σ : ℝ}, (1 : ℝ) / 2 ≤ σ →
    Integrable (fun x => ‖F x‖ * δ x ^ σ) μ → Integrable (fun x => ‖Fd x‖ * δd x ^ σ) μ' →
    ∀ {N Nd D Dd E H m md : ℂ → ℂ},
    (∀ s : ℂ, s.re = σ → N s = D s * ∫ x, F x * (δ x : ℂ) ^ s ∂μ) →
    (∀ s : ℂ, s.re = σ → Nd s = Dd s * ∫ x, Fd x * (δd x : ℂ) ^ s ∂μ') →
    (∀ s : ℂ, Nd (1 - s) = E s * N s) →
    Differentiable ℂ (fun s => N s * E s * H s) → StripDecay (fun s => N s * E s * H s) →
    Differentiable ℂ m → Differentiable ℂ md → StripDecay m → StripDecay md →
    (∀ s : ℂ, m (-s) = D s * E s * H s) → (∀ s : ℂ, md (s - 1) = Dd (1 - s) * H s) →
    ∀ {b : ℝ}, 0 < b →
      theta μ F δ (mellinInv 0 m) b = (b : ℂ) * theta μ' Fd δd (mellinInv 0 md) b⁻¹

theorem theta_mellinInv_reflection : ArchimedeanMellinWeightedReflectionStatement.{u, v} := by
  intro X X' _ _ μ μ' _ _ F δ Fd δd hF hFd hδ hδd hpos hposd σ hσ hI hId N Nd D Dd E H m md
    hOrd hRef hFE hDiff hDecay hm hmd hmD hmdD hmEq hmdEq b hb
  let c : ℝ := 1 / (2 * π)
  let J (s : ℂ) := (b : ℂ) ^ s * (N s * E s * H s)
  let z (y : ℝ) : ℂ := ((-σ : ℝ) : ℂ) + y * I
  have hJdiff : Differentiable ℂ J := fun s =>
    (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hb.ne'))).mul (hDiff s)
  have hshift : (∫ y : ℝ, J (((1 - σ : ℝ) : ℂ) + y * I)) = ∫ y : ℝ, J ((σ : ℂ) + y * I) := by
    obtain ⟨C, hC⟩ := hDecay (1 - σ) σ
    refine integral_vertical_eq hJdiff (by linarith) (C := (b ^ (1 - σ) + b ^ σ) * C) ?_
    intro x hx hx' y
    let u : ℂ := (x : ℂ) + y * I
    have hr : u.re = x := by simp [u]
    change ‖(b : ℂ) ^ u * (N u * E u * H u)‖ ≤ _
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hb, hr]
    calc
      _ ≤ (b ^ (1 - σ) + b ^ σ) * (C * (1 + y ^ 2)⁻¹) :=
        mul_le_mul (rpow_le_add hb hx hx') (hC x hx hx' y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hleft : theta μ F δ (mellinInv 0 m) b = c • ∫ y : ℝ, J ((σ : ℂ) + y * I) := by
    rw [theta_mellinInv_line μ hF hδ hpos hm hmD σ hI hb]
    apply congrArg (c • ·)
    rw [← integral_comp_neg_real (fun y => J ((σ : ℂ) + y * I))]
    apply integral_congr_ae
    refine ae_of_all _ fun y => ?_
    have hz : -z y = (σ : ℂ) + ((-y : ℝ) : ℂ) * I := by simp [z]; ring
    have hr : (-z y).re = σ := by simp [z]
    change (b : ℂ) ^ (-z y) * (∫ x, F x * (δ x : ℂ) ^ (-z y) ∂μ) * m (z y) =
      J ((σ : ℂ) + ((-y : ℝ) : ℂ) * I)
    rw [← hz]
    have hM : m (z y) = D (-z y) * E (-z y) * H (-z y) := by simpa using hmEq (-z y)
    simp only [J, hM, hOrd (-z y) hr]
    ring
  have hright : (b : ℂ) * theta μ' Fd δd (mellinInv 0 md) b⁻¹ =
      c • ∫ y : ℝ, J (((1 - σ : ℝ) : ℂ) + y * I) := by
    rw [theta_mellinInv_line μ' hFd hδd hposd hmd hmdD σ hId (inv_pos.mpr hb)]
    simp only [Complex.real_smul]
    change (b : ℂ) * ((c : ℂ) * ∫ y : ℝ, ((b⁻¹ : ℝ) : ℂ) ^ (-z y) *
      (∫ x, Fd x * (δd x : ℂ) ^ (-z y) ∂μ') * md (z y)) = _
    rw [mul_left_comm (b : ℂ), ← integral_const_mul]
    apply congrArg ((c : ℂ) * ·)
    apply integral_congr_ae
    refine ae_of_all _ fun y => ?_
    have hz : ((1 - σ : ℝ) : ℂ) + y * I = 1 + z y := by simp [z]; ring
    have hM : md (z y) = Dd (-z y) * H (1 + z y) := by simpa using hmdEq (1 + z y)
    have hr : (-z y).re = σ := by simp [z]
    change (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) ^ (-z y) *
      (∫ x, Fd x * (δd x : ℂ) ^ (-z y) ∂μ') * md (z y)) = J (((1 - σ : ℝ) : ℂ) + y * I)
    rw [hz, hM]
    simp only [J]
    have hN : E (1 + z y) * N (1 + z y) = Nd (-z y) := by simpa using (hFE (1 + z y)).symm
    rw [show N (1 + z y) * E (1 + z y) = E (1 + z y) * N (1 + z y) from mul_comm _ _, hN, hRef (-z y) hr]
    rw [show (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) ^ (-z y) *
        (∫ x, Fd x * (δd x : ℂ) ^ (-z y) ∂μ') * (Dd (-z y) * H (1 + z y))) =
        ((b : ℂ) * ((b⁻¹ : ℝ) : ℂ) ^ (-z y)) *
        ((∫ x, Fd x * (δd x : ℂ) ^ (-z y) ∂μ') * Dd (-z y) * H (1 + z y)) by ring]
    rw [cpow_reflection_scale hb]
    ring
  rw [hleft, hright, hshift]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
