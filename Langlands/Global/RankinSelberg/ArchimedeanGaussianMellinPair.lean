import Langlands.Global.RankinSelberg.ArchimedeanMellinWeightedReflection

/-! # Mellin pair weights with an arbitrary positive Gaussian rate -/

noncomputable section

open Complex

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin

open ArchimedeanMellinPair (RapidDecay)

/-- The common Mellin multiplier with a positive Gaussian rate and a real linear shift. -/
def gaussianFactor (rate B : ℝ) (s : ℂ) : ℂ := Complex.exp ((rate : ℂ) * s ^ 2 + (B : ℂ) * s)

theorem differentiable_gaussianFactor (rate B : ℝ) : Differentiable ℂ (gaussianFactor rate B) :=
  (((differentiable_id.pow 2).const_mul (rate : ℂ)).add (differentiable_id.const_mul (B : ℂ))).cexp

/-- A positive Gaussian rate makes a strip exponential bound integrable on vertical lines. -/
theorem stripDecay_gaussianFactor_mul {f : ℂ → ℂ} (hf : StripExpType f) {rate : ℝ} (hrate : 0 < rate) (B : ℝ) :
    StripDecay (fun s => gaussianFactor rate B s * f s) := by
  intro a b
  obtain ⟨C, K, hC, hK, hF⟩ := hf a b
  let M := rate * (a ^ 2 + b ^ 2) + |B| * (|a| + |b|) + (K + 1) ^ 2 / (4 * rate)
  refine ⟨2 * C * Real.exp M, fun x hax hxb y => ?_⟩
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hxsq : x ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total 0 x with h | h <;> nlinarith
  have hBx : B * x ≤ |B| * (|a| + |b|) := calc
    _ ≤ |B| * |x| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (abs_nonneg B)
  have hky : (K + 1) * |y| - rate * y ^ 2 ≤ (K + 1) ^ 2 / (4 * rate) := by
    rw [← sq_abs y]
    apply (le_div_iff₀ (show 0 < 4 * rate by positivity)).mpr
    nlinarith only [sq_nonneg (2 * rate * |y| - (K + 1))]
  have hRe : (((rate : ℂ) * ((x : ℂ) + y * I) ^ 2 + (B : ℂ) * ((x : ℂ) + y * I))).re =
      rate * (x ^ 2 - y ^ 2) + B * x := by simp [sq]
  simp only [norm_mul, gaussianFactor, norm_exp, hRe]
  calc
    _ ≤ Real.exp (rate * (x ^ 2 - y ^ 2) + B * x) * (C * Real.exp (K * |y|)) :=
      mul_le_mul_of_nonneg_left (hF x hax hxb y) (Real.exp_nonneg _)
    _ = C * Real.exp (rate * (x ^ 2 - y ^ 2) + B * x + K * |y|) := by
      rw [Real.exp_add (rate * (x ^ 2 - y ^ 2) + B * x) (K * |y|)]
      ring
    _ ≤ C * Real.exp (M - |y|) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      have hratex := mul_le_mul_of_nonneg_left hxsq hrate.le
      dsimp only [M]
      linarith [hratex, hBx, hky]
    _ = C * Real.exp M * Real.exp (-|y|) := by rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
    _ ≤ _ := by
      calc
        _ ≤ C * Real.exp M * (2 * (1 + y ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (exp_neg_abs_le y) (by positivity)
        _ = _ := by ring

theorem StripExpType.comp_neg {f : ℂ → ℂ} (hf : StripExpType f) : StripExpType (fun s => f (-s)) :=
  (hf.comp_ofReal_mul (-1)).congr fun s => by simp

theorem StripExpType.comp_one_sub {f : ℂ → ℂ} (hf : StripExpType f) : StripExpType (fun s => f (1 - s)) :=
  (hf.comp_neg.comp_add (-1)).congr fun s => by simp [sub_eq_add_neg, add_comm]

/-- Spectral function used for the ordinary inverse Mellin weight. -/
def gaussianOrdinaryTransform (D E : ℂ → ℂ) (rate B : ℝ) (u : ℂ) : ℂ :=
  D (-u) * E (-u) * gaussianFactor rate B (-u)

/-- Spectral function used for the reflected inverse Mellin weight. -/
def gaussianReflectedTransform (Dd : ℂ → ℂ) (rate B : ℝ) (u : ℂ) : ℂ :=
  Dd (-u) * gaussianFactor rate B (1 + u)

theorem gaussianOrdinaryTransform_spec (D E : ℂ → ℂ) {rate : ℝ} (hrate : 0 < rate) (B : ℝ)
    (hD : Differentiable ℂ D) (hE : Differentiable ℂ E) (hDt : StripExpType D) (hEt : StripExpType E) :
    Differentiable ℂ (gaussianOrdinaryTransform D E rate B) ∧ StripDecay (gaussianOrdinaryTransform D E rate B) := by
  refine ⟨((hD.comp differentiable_neg).mul (hE.comp differentiable_neg)).mul
    ((differentiable_gaussianFactor rate B).comp differentiable_neg), ?_⟩
  refine (stripDecay_gaussianFactor_mul (hDt.comp_neg.mul hEt.comp_neg) hrate (-B)).congr fun s => ?_
  have h : gaussianFactor rate (-B) s = gaussianFactor rate B (-s) := by simp [gaussianFactor]
  rw [gaussianOrdinaryTransform, h, mul_comm]

theorem gaussianReflectedTransform_spec (Dd : ℂ → ℂ) {rate : ℝ} (hrate : 0 < rate) (B : ℝ)
    (hD : Differentiable ℂ Dd) (hDt : StripExpType Dd) :
    Differentiable ℂ (gaussianReflectedTransform Dd rate B) ∧ StripDecay (gaussianReflectedTransform Dd rate B) := by
  refine ⟨(hD.comp differentiable_neg).mul
    ((differentiable_gaussianFactor rate B).comp (differentiable_id.const_add 1)), ?_⟩
  refine ((stripDecay_gaussianFactor_mul hDt.comp_one_sub hrate B).comp_add_ofReal 1).congr fun s => ?_
  simp only [ofReal_one, gaussianReflectedTransform]
  rw [show 1 - (s + 1) = -s by ring, add_comm s, mul_comm]

/-- Inverse Mellin weights for the two reciprocal gamma products with common Gaussian multiplier. -/
def ArchimedeanGaussianMellinPairStatement : Prop :=
  ∀ (D Dd E : ℂ → ℂ) (rate B : ℝ), 0 < rate →
    Differentiable ℂ D → Differentiable ℂ Dd → Differentiable ℂ E →
    StripExpType D → StripExpType Dd → StripExpType E →
    let h := mellinInv 0 (gaussianOrdinaryTransform D E rate B)
    let k := mellinInv 0 (gaussianReflectedTransform Dd rate B)
    Measurable h ∧ Measurable k ∧ RapidDecay h ∧ RapidDecay k ∧
      (∀ s : ℂ, mellin h (-s) = D s * E s * gaussianFactor rate B s) ∧
      (∀ s : ℂ, mellin k (s - 1) = Dd (1 - s) * gaussianFactor rate B s)

theorem archimedeanGaussianMellinPair : ArchimedeanGaussianMellinPairStatement := by
  intro D Dd E rate B hrate hD hDd hE hDt hDdt hEt
  obtain ⟨hm, hmt⟩ := gaussianOrdinaryTransform_spec D E hrate B hD hE hDt hEt
  obtain ⟨hmd, hmdt⟩ := gaussianReflectedTransform_spec Dd hrate B hDd hDdt
  exact ⟨measurable_mellinInv hm.continuous _, measurable_mellinInv hmd.continuous _,
    rapidDecay_mellinInv hm hmt, rapidDecay_mellinInv hmd hmdt,
    fun s => by rw [mellin_mellinInv hm hmt]; simp [gaussianOrdinaryTransform],
    fun s => by
      rw [mellin_mellinInv hmd hmdt, gaussianReflectedTransform, show -(s - 1) = 1 - s by ring,
        show 1 + (s - 1) = s by ring]⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin
