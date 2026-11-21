import Langlands.Global.RankinSelberg.RealGodementSchwartzMajorant
import Langlands.Global.ArchimedeanCharacterGrowth
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy

/-! # Initial convergence of the real square matrix integral -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal

local instance realMatrixZetaGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realMatrixZetaGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ

private theorem norm_entry_le_matrixNorm (X : Mat) (i j : I) : ‖X i j‖ ≤ ‖X‖ := by
  change (‖X i j‖₊ : ℝ) ≤ (‖X‖₊ : ℝ)
  rw [NNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
  exact (Finset.single_le_sum (f := fun l => ‖X i l‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun l => ∑ j : I, ‖X l j‖₊) (Finset.mem_univ i))

private theorem norm_det_le_size_real (X : Mat) :
    ‖X.det‖ ≤ (Nat.factorial n : ℝ) * (1 + ‖X‖) ^ n :=
  Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos _) X _
    (fun i j => (norm_entry_le_matrixNorm X i j).trans (le_add_of_nonneg_left zero_le_one))

private theorem norm_adjugate_entry_le_size_real (X : Mat) (i j : I) :
    ‖X.adjugate i j‖ ≤ (Nat.factorial n : ℝ) * (1 + ‖X‖) ^ n := by
  rw [Matrix.adjugate_apply]
  apply Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos _)
  intro k l
  by_cases hk : k = j
  · subst k
    rw [Matrix.updateRow_self]
    simp only [Pi.single_apply]
    split
    · simpa only [norm_one] using (le_add_of_nonneg_right (norm_nonneg X))
    · simpa only [norm_zero] using (add_nonneg zero_le_one (norm_nonneg X))
  · rw [Matrix.updateRow_ne hk]
    exact (norm_entry_le_matrixNorm X k l).trans (le_add_of_nonneg_left zero_le_one)

private theorem norm_det_mul_inv_entry_real (g : G) (i j : I) :
    ‖g.val.det‖ * ‖(g⁻¹).val i j‖ = ‖g.val.adjugate i j‖ := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, norm_mul, norm_inv, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)), one_mul]

/-- Squaring the real determinant modulus cancels the inverse-entry denominators in the height. -/
theorem realMatrixHeight_mul_absDet_sq_bound (g : G) :
    realMatrixHeight g * |g.val.det| ^ 2 ≤
      (2 * (n : ℝ) ^ 2 * (Nat.factorial n : ℝ) ^ 2) * (1 + ‖g.val‖) ^ (2 * (n + 1)) := by
  let X := g.val
  let P := 1 + ‖X‖
  let F := (Nat.factorial n : ℝ)
  have hP : 1 ≤ P := le_add_of_nonneg_right (norm_nonneg _)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hDet : ‖X.det‖ ≤ F * P ^ n := norm_det_le_size_real X
  have hmain (i j : I) : ‖X i j‖ * ‖X.det‖ ≤ F * P ^ (n + 1) := by
    rw [pow_succ, ← mul_assoc, mul_comm _ P]
    exact mul_le_mul ((norm_entry_le_matrixNorm X i j).trans (le_add_of_nonneg_left zero_le_one))
      hDet (norm_nonneg _) (zero_le_one.trans hP)
  have hadj (i j : I) : ‖X.adjugate i j‖ ≤ F * P ^ (n + 1) :=
    (norm_adjugate_entry_le_size_real X i j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (Nat.le_succ _)) hF)
  rw [← Real.norm_eq_abs]
  unfold realMatrixHeight
  simp only [Finset.sum_mul, add_mul]
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, ((F * P ^ (n + 1)) ^ 2 + (F * P ^ (n + 1)) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      change ‖X i j‖ ^ 2 * ‖X.det‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2 * ‖X.det‖ ^ 2 ≤ _
      rw [← mul_pow, ← mul_pow, mul_comm ‖(g⁻¹).val i j‖, norm_det_mul_inv_entry_real g i j]
      exact add_le_add (pow_le_pow_left₀ (by positivity) (hmain i j) _)
        (pow_le_pow_left₀ (norm_nonneg _) (hadj i j) _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
        ← pow_mul, mul_comm (n + 1) 2, F, P, X]
      push_cast
      ring

private theorem exists_realHeight_detPower_bound (N : ℕ) (q : ℝ)
    (hq : (n : ℝ) + 2 * N ≤ q) :
    ∃ (B : ℝ) (p : ℕ), 0 ≤ B ∧ ∀ g : G,
      realMatrixHeight g ^ N * |g.val.det| ^ (q - (n : ℝ)) ≤ B * (1 + ‖g.val‖) ^ p := by
  let K : ℝ := 2 * (n : ℝ) ^ 2 * (Nat.factorial n : ℝ) ^ 2
  let F : ℝ := (Nat.factorial n : ℝ)
  let t := q - (n : ℝ) - 2 * N
  let b := ⌈t⌉₊
  have ht : 0 ≤ t := by dsimp [t]; linarith
  refine ⟨K ^ N * (1 + F) ^ b, (2 * (n + 1)) * N + n * b, by positivity, fun g => ?_⟩
  let A := |g.val.det|
  let P := 1 + ‖g.val‖
  have hA : 0 < A := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
  have hP : 1 ≤ P := le_add_of_nonneg_right (norm_nonneg _)
  have hAdet : A ≤ F * P ^ n := by simpa only [Real.norm_eq_abs] using norm_det_le_size_real g.val
  have hb : 1 + A ≤ (1 + F) * P ^ n := by
    rw [add_mul, one_mul]
    exact add_le_add (one_le_pow₀ hP) hAdet
  have hDr : A ^ t ≤ ((1 + F) * P ^ n) ^ b := by
    calc
      _ ≤ (1 + A) ^ t := Real.rpow_le_rpow hA.le (le_add_of_nonneg_left zero_le_one) ht
      _ ≤ (1 + A) ^ (b : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right hA.le) (Nat.le_ceil _)
      _ ≤ _ := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (add_nonneg zero_le_one hA.le) hb _
  have hprod : 0 ≤ realMatrixHeight g * A ^ 2 :=
    mul_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) (sq_nonneg _)
  calc
    _ = (realMatrixHeight g * A ^ 2) ^ N * A ^ t := by
      rw [mul_pow, mul_assoc, ← pow_mul, ← Real.rpow_natCast A (2 * N), ← Real.rpow_add hA]
      congr 2
      push_cast
      dsimp [t]
      ring
    _ ≤ (K * P ^ (2 * (n + 1))) ^ N * ((1 + F) * P ^ n) ^ b :=
      mul_le_mul (pow_le_pow_left₀ hprod (realMatrixHeight_mul_absDet_sq_bound g) _) hDr
        (Real.rpow_nonneg hA.le _) (by positivity)
    _ = _ := by
      change (K * P ^ (2 * (n + 1))) ^ N * ((1 + F) * P ^ n) ^ b =
        K ^ N * (1 + F) ^ b * P ^ (2 * (n + 1) * N + n * b)
      rw [mul_pow K, mul_pow (1 + F), mul_mul_mul_comm, ← pow_mul P, ← pow_mul P, ← pow_add]

/-- Weighted norm integrability on any left Haar measure for a measurable coefficient of
polynomial height growth. The exponent includes any normalization shift applied by the caller. -/
theorem integrable_realMatrixWeightedNorm (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : 𝓢(Mat, ℂ))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    {q : ℝ} (hq : (n : ℝ) + 2 * N ≤ q) :
    Integrable (fun g => ‖Φ g.val‖ * ‖f g‖ * |g.val.det| ^ q) μ := by
  obtain ⟨B, p, hB, hPoly⟩ := exists_realHeight_detPower_bound (r := r) N q hq
  obtain ⟨L, hL⟩ := RealGodement.exists_integrable_matrixDecay μ
  let S := (2 : ℝ) ^ (p + L) * (Finset.Iic (p + L, 0)).sup
    (fun ij : ℕ × ℕ => SchwartzMap.seminorm ℝ ij.1 ij.2) Φ
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hΦ (X : Mat) : ‖Φ X‖ * (1 + ‖X‖) ^ p ≤ S * ((1 + ‖X‖) ^ L)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_assoc, ← pow_add, mul_comm ‖Φ X‖]
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (p + L, 0)) (𝕜 := ℝ) le_rfl le_rfl Φ X
  have hm : Measurable (fun g : G => |g.val.det|) :=
    (continuous_abs.comp Units.continuous_val.matrix_det).measurable
  refine (hL.const_mul (C * B * S)).mono'
    ((((Φ.continuous.measurable.comp Units.continuous_val.measurable).norm.mul hf.norm).mul
      (hm.pow_const q)).aestronglyMeasurable) (ae_of_all _ fun g => ?_)
  have hA : 0 < |g.val.det| := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖Φ g.val‖ * ‖f g‖ * |g.val.det| ^ q)]
  have hq' : |g.val.det| ^ q = |g.val.det| ^ n * |g.val.det| ^ (q - (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hA]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ‖Φ g.val‖ * (C * realMatrixHeight g ^ N) * |g.val.det| ^ q := by gcongr; exact hbound g
    _ = (C * (‖Φ g.val‖ * |g.val.det| ^ n)) *
        (realMatrixHeight g ^ N * |g.val.det| ^ (q - (n : ℝ))) := by rw [hq']; ring
    _ ≤ (C * (‖Φ g.val‖ * |g.val.det| ^ n)) * (B * (1 + ‖g.val‖) ^ p) :=
      mul_le_mul_of_nonneg_left (hPoly g) (by positivity)
    _ = (C * B * |g.val.det| ^ n) * (‖Φ g.val‖ * (1 + ‖g.val‖) ^ p) := by ring
    _ ≤ (C * B * |g.val.det| ^ n) * (S * ((1 + ‖g.val‖) ^ L)⁻¹) :=
      mul_le_mul_of_nonneg_left (hΦ g.val) (by positivity)
    _ = _ := by ring

/-- The determinant weight has norm equal to the corresponding real power. -/
theorem norm_realDetPower {m : ℕ} (g : GeneralLinear m ℝ) (s : ℂ) :
    ‖detPower realNormalizedAbs g s‖ = |g.val.det| ^ s.re := by
  rw [ArchimedeanLocal.detPower, Complex.norm_exp, Complex.mul_re,
    Real.rpow_def_of_pos (abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g))]
  simp only [realNormalizedAbs, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

private theorem measurable_realLogDet : Measurable (fun g : G => Real.log |g.val.det|) :=
  Real.measurable_log.comp (continuous_abs.comp Units.continuous_val.matrix_det).measurable

/-- The real square matrix kernel at a total exponent `s` is integrable on its initial
right half-plane. The normalized integral uses the total exponent `s + r/2`. -/
theorem integrable_realMatrixZetaKernel (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : 𝓢(Mat, ℂ))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    {s : ℂ} (hs : (n : ℝ) + 2 * N ≤ s.re) :
    Integrable (fun g => Φ g.val * f g * detPower realNormalizedAbs g s) μ := by
  have hm : Measurable (fun g : G => detPower realNormalizedAbs g s) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp measurable_realLogDet))
  exact (integrable_realMatrixWeightedNorm μ hf Φ hC hbound hs).mono'
    ((((Φ.continuous.measurable.comp Units.continuous_val.measurable).mul hf).mul hm).aestronglyMeasurable)
    (ae_of_all _ fun g => by rw [norm_mul, norm_mul, norm_realDetPower])

/-- Holomorphy on the open right half-plane of initial absolute convergence. -/
theorem differentiableOn_realMatrixZetaIntegral (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : 𝓢(Mat, ℂ))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ g, Φ g.val * f g * detPower realNormalizedAbs g s ∂μ)
      {s : ℂ | (n : ℝ) + 2 * N < s.re} :=
  differentiableOn_integral_mul_cexp measurable_realLogDet (isOpen_lt continuous_const Complex.continuous_re)
    (fun s hs => integrable_realMatrixZetaKernel μ hf Φ hC hbound (show (n : ℝ) + 2 * N < s.re from hs).le)

/-- Initial absolute convergence and holomorphy of the real square matrix integral for every
measurable coefficient with a fixed polynomial height bound. -/
def RealMatrixInitialConvergenceStatement : Prop :=
  ∀ (μ : Measure G), ∀ [μ.IsHaarMeasure],
    ∀ (f : G → ℂ) (Φ : 𝓢(Mat, ℂ)) (C : ℝ) (N : ℕ),
      Measurable f → 0 ≤ C → (∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N) →
      let J (s : ℂ) (g : G) := Φ g.val * f g * detPower realNormalizedAbs g s
      (∀ q : ℝ, (n : ℝ) + 2 * N ≤ q → Integrable (fun g => ‖Φ g.val‖ * ‖f g‖ * |g.val.det| ^ q) μ) ∧
      (∀ s : ℂ, (n : ℝ) + 2 * N ≤ s.re → Integrable (J s) μ) ∧
        DifferentiableOn ℂ (fun s : ℂ => ∫ g, J s g ∂μ) {s : ℂ | (n : ℝ) + 2 * N < s.re}

theorem realMatrixInitialConvergence : RealMatrixInitialConvergenceStatement (r := r) := by
  intro μ hμ f Φ C N hf hC hb J
  exact ⟨fun _ hq => integrable_realMatrixWeightedNorm μ hf Φ hC hb hq,
    fun _ hs => integrable_realMatrixZetaKernel μ hf Φ hC hb hs,
    differentiableOn_realMatrixZetaIntegral μ hf Φ hC hb⟩

end Langlands.GodementJacquet
