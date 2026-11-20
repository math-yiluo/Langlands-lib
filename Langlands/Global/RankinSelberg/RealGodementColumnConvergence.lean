import Langlands.Global.RankinSelberg.RealGodementColumnBounds
import Langlands.Global.RankinSelberg.RealGodementFirstColumn
import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel

/-! # Absolute convergence and holomorphy of the real Godement column integral -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis
open Langlands.Global.RankinSelbergGlobal.RealIwasawa
open Langlands.RankinSelberg.GLDeterminantDensity
open MeasureTheory
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {t : ℕ}

private local instance (t : ℕ) : MeasurableSpace (Langlands.GeneralLinear (t + 1) ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (Langlands.GeneralLinear (t + 1) ℝ) := ⟨rfl⟩

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "ColumnSpace" => EuclideanSpace ℝ (Fin (t + 1))
local notation "F" => EuclideanSpace ℝ (Fin (t + 1) × Fin (t + 1))

/-- The first-column kernel with a prescribed determinant parity. -/
def columnMellinBase (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (p : ℕ) (h : G) : ℂ :=
  firstColumnFourier a Φ (columnFrequency h) h.val * W (columnRepresentative h) *
    (((h.val.det / |h.val.det| : ℝ) : ℂ) ^ p)

/-- The Mellin weight in the lower general-linear variable. -/
def columnMellinIntegrand (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (p : ℕ) (s : ℂ) (h : G) : ℂ :=
  columnMellinBase a Φ W p h * Complex.exp (s * (Real.log |h.val.det| : ℂ))

private theorem norm_columnMellinBase (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (p : ℕ) (h : G) :
    ‖columnMellinBase a Φ W p h‖ =
      ‖firstColumnFourier a Φ (columnFrequency h) h.val‖ * ‖W (columnRepresentative h)‖ := by
  have hdet : |h.val.det| ≠ 0 := abs_ne_zero.mpr (determinant h).ne_zero
  simp only [columnMellinBase, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_abs, div_self hdet, one_pow, mul_one]

private theorem continuous_columnMellinBase {W : G → ℂ} (hW : Continuous W)
    (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (p : ℕ) : Continuous (columnMellinBase a Φ W p) := by
  have hFreq : Continuous (columnFrequency (t := t)) := by
    unfold columnFrequency
    exact (Units.continuous_val.comp (continuous_inverseTranspose (t + 1) ℝ)).matrix_mulVec continuous_const
  have hΦ := (realGodementFirstColumn (t + 1) a Φ).1.comp (hFreq.prodMk Units.continuous_val)
  have hRep : Continuous (columnRepresentative (t := t)) := continuous_const.mul continuous_inv
  have hDet : Continuous (fun h : G => h.val.det) := Units.continuous_val.matrix_det
  have hSign := hDet.div hDet.abs (fun h => abs_ne_zero.mpr (determinant h).ne_zero)
  exact (hΦ.mul (hW.comp hRep)).mul ((Complex.continuous_ofReal.comp hSign).pow p)

private def matrixEntryNorm (A : M) : ℝ := ‖(WithLp.toLp 2 (Function.uncurry A) : F)‖

open scoped Matrix.Norms.Frobenius in
private theorem norm_uncurry_eq_frobenius (A : M) :
    matrixEntryNorm A = ‖A‖ := by
  unfold matrixEntryNorm
  rw [PiLp.norm_eq_of_L2, Fintype.sum_prod_type, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rfl

private theorem norm_columnRepresentative (a : ℝˣ) {W : G → ℂ}
    (hW : W ∈ RealLocalWhittaker.regularFunctions t (-a)) (h : G) :
    ‖W (columnRepresentative h)‖ =
      ‖W (torus (alpha (columnRepresentative h)) * (kpart (columnRepresentative h)).val)‖ := by
  let g := columnRepresentative h
  let u := npart g
  let k := torus (alpha g) * (kpart g).val
  have he : u.val * k = g := by
    dsimp only [k, u]
    rw [← mul_assoc, npart_mul_torus_mul_kpart]
  change ‖W g‖ = ‖W k‖
  rw [← he, hW.1 u.val u.property k, norm_mul, realWhittakerCharacter,
    UnitaryAdditiveCharacter.norm_complex, one_mul]

private theorem columnMellin_majorant (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hreg : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hgrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W)
    (p L : ℕ) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : G, ‖columnMellinBase a Φ W p h‖ * Real.exp (β * Real.log |h.val.det|) ≤
      C * (|h.val.det| ^ (t + 1) * ((1 + matrixEntryNorm h.val) ^ L)⁻¹) := by
  obtain ⟨N, hN⟩ := RealWhittakerGauge.exists_gauge_bound hreg hgrowth
  let m : ℝ := (t + 1 : ℕ)
  let Q : ℕ := ⌈m * ((N : ℝ) + |β - m|)⌉₊
  have hQ : m * ((N : ℝ) + |β - m|) ≤ Q := Nat.le_ceil _
  obtain ⟨C_W, hC_W, hCW⟩ := hN Q
  obtain ⟨C_Φ, hC_Φ, hCΦ⟩ := (realGodementFirstColumn (t + 1) a Φ).2.1 (Q + L)
  let C := C_Φ * C_W * m ^ (Q + Q)
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos t
  refine ⟨C, mul_nonneg (mul_nonneg hC_Φ hC_W) (pow_nonneg (zero_le_one.trans hm) _), ?_⟩
  intro h
  let y := alpha (columnRepresentative h)
  let R := rootPos y
  let S := ∑ j, |y j|
  let A := 1 + matrixEntryNorm h.val
  let B := 1 + ‖(WithLp.toLp 2 (columnFrequency h) : ColumnSpace)‖
  let D := |h.val.det|
  have hA : 1 ≤ A := le_add_of_nonneg_right (norm_nonneg _)
  have hB : 1 ≤ B := le_add_of_nonneg_right (norm_nonneg _)
  have hDA : 0 < D := abs_pos.mpr (determinant h).ne_zero
  have hLogA : 0 ≤ Real.log (m * A) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hm hA)
  have hLogB : 0 ≤ Real.log (m * B) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hm hB)
  have hSum : S ≤ m * (Real.log (m * A) + Real.log (m * B) + R) :=
    sum_abs_alpha_columnRepresentative h
  have hLogDet : |Real.log D| ≤ S := by
    dsimp only [D, S, y]
    rw [log_det_columnRepresentative, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hDet : (β - m) * Real.log D ≤ |β - m| * S := by
    calc
      _ ≤ |(β - m) * Real.log D| := le_abs_self _
      _ = |β - m| * |Real.log D| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hLogDet (abs_nonneg _)
  have hExp : -(Q : ℝ) * R + (N : ℝ) * S + (β - m) * Real.log D ≤
      (Q : ℝ) * (Real.log (m * A) + Real.log (m * B)) := by
    let T := Real.log (m * A) + Real.log (m * B) + R
    have hT : 0 ≤ T := add_nonneg (add_nonneg hLogA hLogB) (rootPos_nonneg y)
    calc
      _ ≤ -(Q : ℝ) * R + ((N : ℝ) + |β - m|) * S := by linarith
      _ ≤ -(Q : ℝ) * R + ((N : ℝ) + |β - m|) * (m * T) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hSum (by positivity))
      _ = -(Q : ℝ) * R + (m * ((N : ℝ) + |β - m|)) * T := by ring
      _ ≤ -(Q : ℝ) * R + (Q : ℝ) * T := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hQ hT)
      _ = _ := by dsimp only [T]; ring
  have hW0 : W ∈ RealLocalWhittaker.regularFunctions t (-a) := hreg []
  have hWBound : ‖W (columnRepresentative h)‖ ≤ C_W * Real.exp (-(Q : ℝ) * R + (N : ℝ) * S) := by
    rw [norm_columnRepresentative a hW0]
    exact hCW y (kpart (columnRepresentative h))
  have hApos := lt_of_lt_of_le zero_lt_one hA
  have hBpos := lt_of_lt_of_le zero_lt_one hB
  have hmpos := lt_of_lt_of_le zero_lt_one hm
  have hWDet : ‖W (columnRepresentative h)‖ * Real.exp ((β - m) * Real.log D) ≤
      C_W * ((m * A) ^ Q * (m * B) ^ Q) := by
    calc
      _ ≤ (C_W * Real.exp (-(Q : ℝ) * R + (N : ℝ) * S)) * Real.exp ((β - m) * Real.log D) :=
        mul_le_mul_of_nonneg_right hWBound (Real.exp_nonneg _)
      _ = C_W * Real.exp (-(Q : ℝ) * R + (N : ℝ) * S + (β - m) * Real.log D) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ C_W * Real.exp ((Q : ℝ) * (Real.log (m * A) + Real.log (m * B))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hC_W
      _ = _ := by
        rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log (mul_pos hmpos hApos), Real.exp_log (mul_pos hmpos hBpos)]
  let P := ‖firstColumnFourier a Φ (columnFrequency h) h.val‖
  have hP : A ^ (Q + L) * B ^ (Q + L) * P ≤ C_Φ := by
    have hh := hCΦ (columnFrequency h) h.val
    rw [mul_comm ((1 + ‖(WithLp.toLp 2 (columnFrequency h) : ColumnSpace)‖) ^ (Q + L))] at hh
    exact hh
  have hP' : A ^ (Q + L) * B ^ Q * P ≤ C_Φ :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_add_right Q L)) (pow_nonneg hApos.le _))
      (norm_nonneg _)).trans hP
  have hComb : P * (‖W (columnRepresentative h)‖ * Real.exp ((β - m) * Real.log D)) ≤ C * (A ^ L)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hApos _)).mpr
    calc
      _ ≤ P * (C_W * ((m * A) ^ Q * (m * B) ^ Q)) * A ^ L := by
        gcongr
      _ = (C_W * m ^ (Q + Q)) * (A ^ (Q + L) * B ^ Q * P) := by
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring
      _ ≤ (C_W * m ^ (Q + Q)) * C_Φ :=
        mul_le_mul_of_nonneg_left hP' (mul_nonneg hC_W (pow_nonneg hmpos.le _))
      _ = C := by
        dsimp only [C]
        ring
  have hDetExp : Real.exp (β * Real.log D) = D ^ (t + 1) * Real.exp ((β - m) * Real.log D) := by
    rw [show β * Real.log D = (m : ℝ) * Real.log D + (β - m) * Real.log D by ring,
      Real.exp_add]
    change Real.exp (((t + 1 : ℕ) : ℝ) * Real.log D) * _ = _
    rw [Real.exp_nat_mul, Real.exp_log hDA]
  rw [norm_columnMellinBase]
  change P * ‖W (columnRepresentative h)‖ * Real.exp (β * Real.log D) ≤ C * (D ^ (t + 1) * (A ^ L)⁻¹)
  rw [hDetExp]
  calc
    _ = D ^ (t + 1) * (P * (‖W (columnRepresentative h)‖ * Real.exp ((β - m) * Real.log D))) := by ring
    _ ≤ D ^ (t + 1) * (C * (A ^ L)⁻¹) := mul_le_mul_of_nonneg_left hComb (pow_nonneg hDA.le _)
    _ = _ := by ring

private theorem continuous_logAbsDet : Continuous (fun h : G => Real.log |h.val.det|) :=
  Units.continuous_val.matrix_det.abs.log (fun h => abs_ne_zero.mpr (determinant h).ne_zero)

open scoped Matrix.Norms.Frobenius in
private theorem exists_integrable_columnDensity (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ L : ℕ, Integrable (fun h : G => |h.val.det| ^ (t + 1) * ((1 + matrixEntryNorm h.val) ^ L)⁻¹) μ := by
  obtain ⟨c, hc, hμ⟩ := exists_realMatrixHaar_eq_smul μ
  let ν := realMatrixVolume (t + 1)
  let : ν.IsAddHaarMeasure := by
    change (realMatrixVolume (t + 1)).IsAddHaarMeasure
    unfold realMatrixVolume
    infer_instance
  let L := ν.integrablePower
  let b : M → ℝ := fun A => ((1 + ‖A‖) ^ L)⁻¹
  have hb : Integrable b ν := (ν.integrable_pow_neg_integrablePower).congr
    (Filter.Eventually.of_forall fun A => by
      simp only [b, L, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖A‖), Real.rpow_natCast])
  have hAdd : Integrable (fun h : G => |h.val.det| ^ (t + 1) * b h.val) μ := by
    unfold realMatrixHaar at hμ
    have h := (integrable_forwardWeight_iff_of_eq_smul (K := ℝ) (E := ℝ) (t + 1)
      nnnormHom continuous_nnnorm ν μ c hc hμ b).2 hb.integrableOn
    simpa only [forwardWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow,
      nnnormHom_apply, coe_nnnorm, Real.norm_eq_abs] using h
  exact ⟨L, by simpa only [norm_uncurry_eq_frobenius, b] using hAdd⟩

private theorem integrable_columnMellinNorm (μ : Measure G) [μ.IsHaarMeasure]
    (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hreg : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hgrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W) (p : ℕ) (β : ℝ) :
    Integrable (fun h : G => ‖columnMellinBase a Φ W p h‖ * Real.exp (β * Real.log |h.val.det|)) μ := by
  obtain ⟨L, hAdd⟩ := exists_integrable_columnDensity μ
  obtain ⟨C, _, hC⟩ := columnMellin_majorant a Φ W hreg hgrowth p L β
  have hW0 : W ∈ RealLocalWhittaker.regularFunctions t (-a) := hreg []
  have hB := continuous_columnMellinBase hW0.2.1.continuous a Φ p
  have hExp := Real.continuous_exp.comp ((continuous_logAbsDet (t := t)).const_mul β)
  refine (hAdd.const_mul C).mono' (hB.norm.mul hExp).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun h => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC h

/-- The real first-column integral is absolutely convergent for every spectral
parameter and entire for fixed lower Whittaker function and Schwartz test. -/
def RealGodementColumnConvergenceStatement : Prop :=
  ∀ (t : ℕ) (μ : Measure (Langlands.GeneralLinear (t + 1) ℝ)) [μ.IsHaarMeasure]
    (a : ℝˣ) (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ))
    (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a)) →
    RealUniformWhittaker.HasUniformDerivativeGrowth W → ∀ p : ℕ,
      (∀ s : ℂ, Integrable (columnMellinIntegrand a Φ W p s) μ) ∧
      Differentiable ℂ (fun s : ℂ => ∫ h, columnMellinIntegrand a Φ W p s h ∂μ)

theorem realGodementColumnConvergence : RealGodementColumnConvergenceStatement := by
  intro t μ _ a Φ W hreg hgrowth p
  have hInt := integrable_columnMellinNorm μ a Φ W hreg hgrowth p
  have hW0 : W ∈ RealLocalWhittaker.regularFunctions t (-a) := hreg []
  have hB := continuous_columnMellinBase hW0.2.1.continuous a Φ p
  have hLog := continuous_logAbsDet (t := t)
  constructor
  · intro s
    have hs := ((Complex.continuous_ofReal.comp hLog).const_mul s).cexp
    refine (hInt s.re).mono' (hB.mul hs).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun h => by
      rw [columnMellinIntegrand, norm_mul, norm_cexp_mul_ofReal]
  · intro s
    have h := differentiableOn_integral_cexp_mul (σ := s.re - 1)
      hB.aestronglyMeasurable hLog.aestronglyMeasurable (fun β _ => hInt β)
    apply h.differentiableAt
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith)

/-- The published uniform real Whittaker model supplies the derivative hypotheses. -/
theorem columnMellin_convergence_of_mem_model (μ : Measure G) [μ.IsHaarMeasure]
    (a : ℝˣ) (Φ : 𝓢(X, ℂ)) {ds : List RealBlock} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel t ds (-a)) (p : ℕ) :
    (∀ s : ℂ, Integrable (columnMellinIntegrand a Φ W p s) μ) ∧
      Differentiable ℂ (fun s : ℂ => ∫ h, columnMellinIntegrand a Φ W p s h ∂μ) :=
  realGodementColumnConvergence t μ a Φ W
    (RealUniformWhittaker.iteratedRightDerivative_mem_regularFunctions hW)
    (RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model hW) p

end Langlands.Global.RankinSelbergGlobal.RealGodement
