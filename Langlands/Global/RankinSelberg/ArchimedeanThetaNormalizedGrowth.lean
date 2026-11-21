import Langlands.Global.RankinSelberg.ArchimedeanStripGrowth
import Langlands.Global.RankinSelberg.ArchimedeanGaussianMellinPair

/-! # Normalized continuation with strip growth from a rapid theta reflection -/

noncomputable section

open MeasureTheory Complex Set

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

open ArchimedeanInverseMellin

private theorem mellin_neg_bounded_on_strip {f : ℝ → ℂ} (hf : RapidDecay f) (hm : Measurable f)
    (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖mellin f (-z)‖ ≤ C := by
  let w (x : ℝ) := (x ^ (-a - 1) + x ^ (-b - 1)) * ‖f x‖
  have hI : IntegrableOn w (Ioi 0) := by
    have hEq : w = (fun x : ℝ => x ^ (-a - 1) * ‖f x‖) + (fun x : ℝ => x ^ (-b - 1) * ‖f x‖) :=
      funext fun x => add_mul (x ^ (-a - 1)) (x ^ (-b - 1)) ‖f x‖
    rw [hEq]
    exact (hf.integrableOn hm (-a - 1)).add (hf.integrableOn hm (-b - 1))
  refine ⟨|∫ x in Ioi (0 : ℝ), w x|, abs_nonneg _, fun z ha hb => ?_⟩
  rw [mellin]
  refine (norm_integral_le_of_norm_le hI ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun x hx => ?_))).trans (le_abs_self _)
  have hx₀ : 0 < x := hx
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx₀, sub_re, neg_re, one_re]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (rpow_le_add hx₀ (a := -b - 1) (b := -a - 1) (by linarith) (by linarith)).trans_eq (add_comm _ _)

private theorem stripQuadraticGrowth_div_exp {T E : ℂ → ℂ}
    (hT : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖T z‖ ≤ C)
    (hE : StripExpType (fun s => (E s)⁻¹)) :
    StripQuadraticGrowth (fun s => T s / (E s * Complex.exp (s ^ 2))) := by
  intro a b
  obtain ⟨A, hA, hTa⟩ := hT a b
  obtain ⟨B, K, hB, hK, hEb⟩ := hE a b
  refine ⟨A * B, K + 1, by positivity, by positivity, fun z ha hb => ?_⟩
  have hEinv : ‖(E z)⁻¹‖ ≤ B * Real.exp (K * |z.im|) := by
    simpa only [re_add_im] using hEb z.re ha hb z.im
  have hRe : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [pow_two]
  have hJ : ‖(Complex.exp (z ^ 2))⁻¹‖ = Real.exp (z.im ^ 2 - z.re ^ 2) := by
    rw [← Complex.exp_neg, norm_exp, neg_re, hRe, neg_sub]
  simp only [div_eq_mul_inv, mul_inv, norm_mul]
  rw [show ‖(Complex.exp (z ^ 2))⁻¹‖ = _ from hJ]
  calc
    _ ≤ A * (B * Real.exp (K * |z.im|) * Real.exp (z.im ^ 2 - z.re ^ 2)) := by
      refine mul_le_mul (hTa z ha hb) ?_ (by positivity) hA
      exact mul_le_mul_of_nonneg_right hEinv (Real.exp_nonneg _)
    _ = A * B * Real.exp (K * |z.im| + (z.im ^ 2 - z.re ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hA hB)
      have hY : |z.im| ≤ 1 + |z.im| ^ 2 := by nlinarith [sq_nonneg (|z.im| - 1 / 2)]
      nlinarith [sq_abs z.im, sq_nonneg z.re, mul_le_mul_of_nonneg_left hY hK]

private theorem vertical_bound_of_mellin {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℂ) (δ : X → ℝ) (hδ : ∀ x, 0 < δ x) {f D α : ℂ → ℂ} (hD : StripExpType D)
    {x y : ℝ} (hα : ∀ z : ℂ, z.re = x → (α z).re = y)
    (hI : Integrable (fun p => ‖F p‖ * δ p ^ y) μ)
    (hEq : ∀ z : ℂ, z.re = x → f z = D z * ∫ p, F p * (δ p : ℂ) ^ α z ∂μ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ z : ℂ, z.re = x → ‖f z‖ ≤ C * Real.exp (K * |z.im|) := by
  obtain ⟨A, K, hA, hK, hDX⟩ := hD x x
  let B := ∫ p, ‖F p‖ * δ p ^ y ∂μ
  have hB : 0 ≤ B := integral_nonneg fun p => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδ p).le _)
  refine ⟨A * B, K, mul_nonneg hA hB, hK, fun z hz => ?_⟩
  have hDz : ‖D z‖ ≤ A * Real.exp (K * |z.im|) := by
    have := hDX z.re hz.ge hz.le z.im
    simpa only [re_add_im] using this
  have hZ : ‖∫ p, F p * (δ p : ℂ) ^ α z ∂μ‖ ≤ B := by
    refine norm_integral_le_of_norm_le hI (ae_of_all _ fun p => ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hδ p), hα z hz]
  rw [hEq z hz, norm_mul]
  calc
    _ ≤ (A * Real.exp (K * |z.im|)) * B := mul_le_mul hDz hZ (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- One rapid theta reflection gives the entire normalized pair with strip exponential type. -/
def ArchimedeanThetaNormalizedGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν → Measurable δ → Measurable δd →
    (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    ∀ (σ : ℝ), (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖F p‖ * δ p ^ x) μ) →
    (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖Fd p‖ * δd p ^ x) ν) →
    ∀ (D Dd E : ℂ → ℂ), StripExpType D → StripExpType Dd → StripExpType E → StripExpType (fun s => (E s)⁻¹) →
    Differentiable ℂ E → (∀ s, E s ≠ 0) →
    ∀ (f fd : ℝ → ℂ), Measurable f → Measurable fd → RapidDecay f → RapidDecay fd →
    (∀ s : ℂ, mellin f (-s) = D s * E s * Complex.exp (s ^ 2)) →
    (∀ s : ℂ, mellin fd (s - 1) = Dd (1 - s) * Complex.exp (s ^ 2)) →
    (∀ b : ℝ, 0 < b → theta μ F δ f b = (b : ℂ) * theta ν Fd δd fd b⁻¹) →
    ∃ N Nd : ℂ → ℂ, Differentiable ℂ N ∧ Differentiable ℂ Nd ∧ StripExpType N ∧ StripExpType Nd ∧
      (∀ s : ℂ, σ ≤ s.re → N s = D s * (∫ p, F p * (δ p : ℂ) ^ s ∂μ) ∧
        Nd s = Dd s * (∫ p, Fd p * (δd p : ℂ) ^ s ∂ν)) ∧
      ∀ s : ℂ, Nd (1 - s) = E s * N s

set_option maxHeartbeats 700000 in
theorem archimedeanThetaNormalizedGrowth : ArchimedeanThetaNormalizedGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ δd hF hFd hδm hδdm hδ hδd σ hI hId D Dd E hDt hDdt hEt hEit hEd hE₀
    f fd hfm hfdm hf hfd hfM hfdM hpair
  let Θ := theta μ F δ f
  let T (s : ℂ) := mellin Θ (-s)
  let J (s : ℂ) := Complex.exp (s ^ 2)
  let N (s : ℂ) := T s / (E s * J s)
  let Nd (s : ℂ) := T (1 - s) / J (1 - s)
  obtain ⟨hTa, hTl, hTr⟩ := mellin_theta_entire μ ν F δ Fd δd hF hFd hδm hδdm hδ hδd f fd
    hfm hfdm hf hfd σ hI hId hpair
  have hΘ : RapidDecay Θ := theta_rapidDecay μ ν F δ Fd δd hδ hδd hf hfd hI hId hpair
  have hΘm : Measurable Θ := by
    have hΘ' : StronglyMeasurable (fun b : ℝ => theta μ F δ f b) := by
      obtain ⟨F₀, hF₀, hEq⟩ := hF
      have hM : Measurable (fun p : ℝ × X => F₀ p.2 * f (p.1 * δ p.2)) :=
        (hF₀.measurable.comp measurable_snd).mul (hfm.comp (measurable_fst.mul (hδm.comp measurable_snd)))
      have hInt : StronglyMeasurable (fun b : ℝ => ∫ p, F₀ p * f (b * δ p) ∂μ) :=
        hM.stronglyMeasurable.integral_prod_right (ν := μ)
      have he : theta μ F δ f = fun b => ∫ p, F₀ p * f (b * δ p) ∂μ := by
        funext b
        apply integral_congr_ae
        filter_upwards [hEq] with p hp
        exact congrArg (fun c => c * f (b * δ p)) hp
      exact he.symm ▸ hInt
    exact hΘ'.measurable
  have hJa : Differentiable ℂ J := (differentiable_id.pow 2).cexp
  have hJ₀ (s : ℂ) : J s ≠ 0 := Complex.exp_ne_zero _
  have hden (s : ℂ) : E s * J s ≠ 0 := mul_ne_zero (hE₀ s) (hJ₀ s)
  have hN : Differentiable ℂ N := hTa.div (hEd.mul hJa) hden
  have hNd : Differentiable ℂ Nd := (hTa.div hJa hJ₀).comp (differentiable_id.const_sub 1)
  have hFE (s : ℂ) : Nd (1 - s) = E s * N s := by
    change T (1 - (1 - s)) / J (1 - (1 - s)) = E s * (T s / (E s * J s))
    rw [sub_sub_cancel]
    field_simp [hE₀ s, hJ₀ s]
  have hAgree (s : ℂ) (hs : σ ≤ s.re) : N s = D s * (∫ p, F p * (δ p : ℂ) ^ s ∂μ) ∧
      Nd s = Dd s * (∫ p, Fd p * (δd p : ℂ) ^ s ∂ν) := by
    constructor
    · change T s / (E s * J s) = _
      dsimp only [T, Θ]
      rw [hTl s hs, hfM s]
      apply (div_eq_iff (hden s)).mpr
      dsimp only [J]
      ring
    · have hs' : (1 - s).re ≤ 1 - σ := by simp only [sub_re, one_re]; linarith
      change T (1 - s) / J (1 - s) = _
      dsimp only [T, Θ]
      rw [hTr (1 - s) hs', hfdM (1 - s), sub_sub_cancel]
      apply (div_eq_iff (hJ₀ (1 - s))).mpr
      dsimp only [J]
      ring
  have hQ : StripQuadraticGrowth N := stripQuadraticGrowth_div_exp (mellin_neg_bounded_on_strip hΘ hΘm) hEit
  have hNt : StripExpType N := by
    refine archimedeanStripGrowth N hN hQ ⟨1 - σ, σ, fun x hx => ?_⟩
    rcases hx with hl | hr
    · refine vertical_bound_of_mellin ν Fd δd hδd (hEit.mul hDdt.comp_one_sub) (α := fun z => 1 - z)
        (y := 1 - x) (fun z hz => by simp [hz]) (hId _ (by linarith)) ?_
      intro z hz
      have hz' : σ ≤ (1 - z).re := by simp only [sub_re, one_re, hz]; linarith
      have hEq := (hAgree (1 - z) hz').2
      rw [show N z = (E z)⁻¹ * Nd (1 - z) by rw [hFE, ← mul_assoc, inv_mul_cancel₀ (hE₀ z), one_mul], hEq]
      ring
    · exact vertical_bound_of_mellin μ F δ hδ hDt (α := id) (fun _ hz => hz) (hI x hr.le)
        (fun z hz => (hAgree z (hz ▸ hr.le)).1)
  have hNdt : StripExpType Nd := (hEt.mul hNt).comp_one_sub.congr fun s => by
    simpa only [sub_sub_cancel] using (hFE (1 - s)).symm
  exact ⟨N, Nd, hN, hNd, hNt, hNdt, hAgree, hFE⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair
