import Langlands.Global.RankinSelberg.RealGodementOpenCellModel
import Langlands.Global.RankinSelberg.RealLowestWeightFourier
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-! # The real rank-two discrete block on the diagonal -/

noncomputable section

open Complex Matrix MeasureTheory
open scoped FourierTransform Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteRankTwoWhittaker

open Langlands.Archimedean Langlands.Archimedean.GramFormula Langlands.Archimedean.PrincipalSeriesExtension
open Langlands.Archimedean.RealGramFunction Langlands.Archimedean.RealStandardNontrivial
open Langlands.Archimedean.PartialJacquet
open Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear RealGodement ArchimedeanLocal

local notation "G" => Langlands.GeneralLinear 2 ℝ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℝ

private def blockTest (d : ComplexCharacterData) : G → ℂ :=
  gramFunction (GramFormula.shiftedExponent 2 (realPositionExponent [.induced d]))
    (blockPoly 2 [.induced d] 0)

private theorem blockTest_mem (d : ComplexCharacterData) :
    blockTest d ∈ Automorphic.realStandardKFinite 2 [.induced d] :=
  gramFunction_blockPoly_mem 2 [.induced d] (by simp [realRank, RealBlock.rank])

private def polarCompact (b : ℝ) (r x ρ : ℝ) : Mat :=
  !![-b * x / ρ, r / ρ; b * r / ρ, x / ρ]

private def polarUpper (r x ρ : ℝ) : Mat :=
  !![r / ρ, x / ρ; 0, ρ]

private theorem polarCompact_mem (b r x ρ : ℝ) (hb : b = 1 ∨ b = -1)
    (hρ : ρ ≠ 0) (hsq : ρ ^ 2 = r ^ 2 + x ^ 2) : polarCompact b r x ρ ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rcases hb with rfl | rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [polarCompact, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
    field_simp [hρ] <;> nlinarith

private theorem polarUpper_mul_compact (b r x ρ : ℝ) (hρ : ρ ≠ 0)
    (hsq : ρ ^ 2 = r ^ 2 + x ^ 2) : polarUpper r x ρ * polarCompact b r x ρ = !![0, 1; b * r, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polarUpper, polarCompact, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hρ] <;> nlinarith

private theorem shiftedExponent_induced_zero (d : ComplexCharacterData) :
    GramFormula.shiftedExponent 2 (realPositionExponent [.induced d]) 0 =
      d.exponent + ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2 := by
  simp [GramFormula.shiftedExponent, realPositionExponent]
  ring

private theorem shiftedExponent_induced_one (d : ComplexCharacterData) :
    GramFormula.shiftedExponent 2 (realPositionExponent [.induced d]) 1 =
      d.exponent - ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2 := by
  simp [GramFormula.shiftedExponent, realPositionExponent]
  ring

private theorem compactBlockPolynomial (d : ComplexCharacterData) (b r x ρ : ℝ)
    (hb : b = 1 ∨ b = -1) (hκ : polarCompact b r x ρ ∈ Matrix.unitaryGroup (Fin 2) ℝ) :
    orthogonalEval (blockPoly 2 [.induced d] 0) ⟨polarCompact b r x ρ, hκ⟩ =
      ((2 * I) * ((r : ℂ) + (b : ℂ) * (x : ℂ) * I) / (ρ : ℂ)) ^ (d.weight.natAbs + 1) := by
  let Y : Fin 2 × Fin 2 → ℂ := fun ij => (polarCompact b r x ρ ij.1 ij.2 : ℂ)
  change MvPolynomial.eval Y (blockPoly 2 [.induced d] 0) = _
  rw [show blockPoly 2 [.induced d] 0 = blockFactor 2 0 (d.weight.natAbs + 1) by simp [blockPoly]]
  rw [eval_blockFactor, eval_lplus (by decide : 0 + 1 < 2), eval_lminus (by decide : 0 + 1 < 2)]
  let N := d.weight.natAbs + 1
  change (Y (0, 0) + Y (1, 1) + I * (Y (0, 1) - Y (1, 0))) ^ N +
    (-1 : ℂ) ^ N * (Y (1, 1) - Y (0, 0) - I * (Y (0, 1) + Y (1, 0))) ^ N = _
  have hN : N ≠ 0 := Nat.succ_ne_zero _
  rcases hb with rfl | rfl
  · have hp : Y (0, 0) + Y (1, 1) + I * (Y (0, 1) - Y (1, 0)) = 0 := by
      simp [Y, polarCompact, ofReal_div, ofReal_neg, neg_div]
    have hm : (-1 : ℂ) * (Y (1, 1) - Y (0, 0) - I * (Y (0, 1) + Y (1, 0))) =
        (2 * I) * ((r : ℂ) + (1 : ℝ) * (x : ℂ) * I) / (ρ : ℂ) := by
      simp only [Y, polarCompact, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val', neg_mul, one_mul, ofReal_div, ofReal_neg, ofReal_one]
      simp only [div_eq_mul_inv]
      linear_combination (-2 * (x : ℂ) * (ρ : ℂ)⁻¹) * I_sq
    rw [hp, zero_pow hN, zero_add, ← mul_pow, hm]
  · have hm : Y (1, 1) - Y (0, 0) - I * (Y (0, 1) + Y (1, 0)) = 0 := by
      simp [Y, polarCompact, ofReal_div, ofReal_neg, neg_div]
    have hp : Y (0, 0) + Y (1, 1) + I * (Y (0, 1) - Y (1, 0)) =
        (2 * I) * ((r : ℂ) + ((-1 : ℝ) : ℂ) * (x : ℂ) * I) / (ρ : ℂ) := by
      simp only [Y, polarCompact, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val', neg_mul, one_mul, ofReal_div, ofReal_neg, ofReal_one]
      simp only [div_eq_mul_inv]
      linear_combination (2 * (x : ℂ) * (ρ : ℂ)⁻¹) * I_sq
    rw [hm, zero_pow hN, mul_zero, add_zero, hp]

private theorem blockTest_openCell (d : ComplexCharacterData) (b r x : ℝ)
    (hb : b = 1 ∨ b = -1) (hr : 0 < r) (g : G) (hg : g.val = !![0, 1; b * r, x]) :
    blockTest d g = (2 * I) ^ (d.weight.natAbs + 1) *
      (r : ℂ) ^ (d.exponent + ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2) *
      ((r : ℂ) - (b : ℂ) * (x : ℂ) * I)⁻¹ ^ (d.weight.natAbs + 1) := by
  let N := d.weight.natAbs + 1
  let ρ := Real.sqrt (r ^ 2 + x ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hsq : ρ ^ 2 = r ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  let B := polarUpper r x ρ
  let K := polarCompact b r x ρ
  have hB : B.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [B, polarUpper]
  have hdiag (i : Fin 2) : 0 < B i i := by
    fin_cases i
    · exact div_pos hr hρ
    · exact hρ
  have ht (i : Fin 2) : B i i ≠ 0 := (hdiag i).ne'
  have hsign : signDiagonal (fun i => B i i) = 1 := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => signReal (B i i)) = 1
    simp only [signReal, hdiag, ite_true, Matrix.diagonal_one]
  have hK : K ∈ Matrix.unitaryGroup (Fin 2) ℝ := polarCompact_mem b r x ρ hb hρ.ne' hsq
  have hG : g.val = B * K := hg.trans (polarUpper_mul_compact b r x ρ hρ.ne' hsq).symm
  let E := GramFormula.shiftedExponent 2 (realPositionExponent [.induced d])
  let P := blockPoly 2 [.induced d] 0
  have hd : blockTest d g =
      (∏ i : Fin 2, ((|B i i| : ℝ) : ℂ) ^ E i) * orthogonalEval P ⟨K, hK⟩ := by
    rw [blockTest, gramFunction_eq_extension, extension_eq E (orthogonalEval P) hB ht hK hG, hsign, one_mul]
  rw [hd, compactBlockPolynomial d b r x ρ hb hK, Fin.prod_univ_two]
  simp only [abs_of_pos (hdiag _), E, shiftedExponent_induced_zero, shiftedExponent_induced_one]
  have hρC : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  let h := d.exponent + (N : ℂ) / 2
  let k := d.exponent - (N : ℂ) / 2
  have hP : (((r / ρ : ℝ) : ℂ)) ^ h * (ρ : ℂ) ^ k = (r : ℂ) ^ h * (ρ : ℂ)⁻¹ ^ N := by
    rw [ofReal_div, div_cpow_ofReal_nonneg hr.le hρ.le, div_eq_mul_inv, mul_assoc,
      mul_comm (((ρ : ℂ) ^ h)⁻¹), ← cpow_neg, ← cpow_add _ _ hρC, show k + -h = -(N : ℂ) by dsimp [h, k]; ring,
      cpow_neg, cpow_natCast, inv_pow]
  let z := (r : ℂ) - (b : ℂ) * (x : ℂ) * I
  let w := (r : ℂ) + (b : ℂ) * (x : ℂ) * I
  have hz : z ≠ 0 := by
    intro he
    have hRe := congrArg Complex.re he
    simp [z, mul_re, mul_im] at hRe
    exact hr.ne' hRe
  have hb2 : (b : ℂ) ^ 2 = 1 := by rcases hb with rfl | rfl <;> norm_num
  have hprod : w * z = (ρ : ℂ) ^ 2 := by
    have hR : (ρ : ℂ) ^ 2 = (r : ℂ) ^ 2 + (x : ℂ) ^ 2 := by exact_mod_cast hsq
    rw [hR]
    calc
      w * z = (r : ℂ) ^ 2 - (b : ℂ) ^ 2 * (x : ℂ) ^ 2 * I ^ 2 := by dsimp [z, w]; ring
      _ = _ := by rw [hb2, I_sq]; ring
  have hratio : (ρ : ℂ)⁻¹ * ((2 * I) * w / (ρ : ℂ)) = (2 * I) * z⁻¹ := by
    field_simp [hρC, hz]
    exact hprod
  change (((r / ρ : ℝ) : ℂ)) ^ h * (ρ : ℂ) ^ k * (((2 * I) * w) / (ρ : ℂ)) ^ N =
    (2 * I) ^ N * (r : ℂ) ^ h * z⁻¹ ^ N
  rw [hP, mul_assoc, ← mul_pow, hratio, mul_pow]
  ring

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

private local instance : Unique (UpperEntryPair 2) where
  default := ⟨(0, 1), by decide⟩
  uniq q := by
    obtain ⟨⟨i, j⟩, hij⟩ := q
    change i < j at hij
    apply Subtype.ext
    fin_cases i <;> fin_cases j
    · exact ((by decide : ¬ (0 : Fin 2) < 0) hij).elim
    · rfl
    · exact ((by decide : ¬ (1 : Fin 2) < 0) hij).elim
    · exact ((by decide : ¬ (1 : Fin 2) < 1) hij).elim

private def unipotentCoordinate : ℝ ≃ᵐ Langlands.GeneralLinear.upperUnipotent 2 ℝ :=
  (MeasurableEquiv.funUnique (UpperEntryPair 2) ℝ).symm.trans
    (upperEntryCoordinates 2 (K := ℝ)).symm.toMeasurableEquiv

private theorem unipotentCoordinate_entry (x : ℝ) : (unipotentCoordinate x).val.val 0 1 = x :=
  upperEntryCoordinates_symm_upper (d := 2) (i := 0) (j := 1) (fun _ => x) (by decide)

private theorem unipotentCoordinate_val (x : ℝ) : (unipotentCoordinate x).val.val = !![1, x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact UpperUnipotent.entry_diag (unipotentCoordinate x) 0
  · exact unipotentCoordinate_entry x
  · exact UpperUnipotent.entry_eq_zero (unipotentCoordinate x) (i := 1) (j := 0) (by decide)
  · exact UpperUnipotent.entry_diag (unipotentCoordinate x) 1

private theorem unipotentCoordinate_measurePreserving :
    MeasurePreserving unipotentCoordinate volume (upperStepHaar 1 (-1)) := by
  have hV : (realSelfDualMeasure (-1)).measure = (volume : Measure ℝ) := by
    simp [realSelfDualMeasure, realScaledMeasure, realStandardMeasure, Langlands.HarmonicAnalysis.AdditiveHaarMeasure.scale]
  have hμ := (measurePreserving_funUnique (realSelfDualMeasure (-1)).measure (UpperEntryPair 2)).symm
  have hE : MeasurePreserving (upperEntryCoordinates 2 (K := ℝ)).symm
      (upperEntryProductMeasure (realSelfDualMeasure (-1)) 2) (upperStepHaar 1 (-1)) :=
    ⟨(upperEntryCoordinates 2 (K := ℝ)).symm.continuous.measurable, rfl⟩
  have h := hE.comp hμ
  rw [hV] at h
  exact h


/-- The rank-one units embedded as the first diagonal entry of the larger group. -/
def diagonalPoint (a : ℝˣ) : G :=
  padGL (by decide : 0 + 1 ≤ 1 + 1) (Langlands.GodementJacquet.tateScalarEquiv ℝ a)

private theorem diagonalPoint_val (a : ℝˣ) : (diagonalPoint a).val = !![(a : ℝ), 0; 0, 1] := by
  have ha : (Langlands.GodementJacquet.tateScalarEquiv ℝ a).val 0 0 = (a : ℝ) := by
    exact (Matrix.det_fin_one ((Langlands.GodementJacquet.tateScalarEquiv ℝ a).val)).symm.trans
      (RealRankZero.det_val_tateScalarEquiv a)
  ext i j
  rw [diagonalPoint, UnequalAnalytic.padGL_apply]
  fin_cases i <;> fin_cases j <;> norm_num [ha, Matrix.one_apply]

private theorem weylLong_two_val : (weylLong 2 ℝ).val = !![0, 1; 1, 0] := by
  ext i j
  change (GeneralLinear.permutation 2 ℝ Fin.revPerm).val i j = _
  rw [GeneralLinear.permutation_entry]
  fin_cases i <;> fin_cases j <;> rfl

private theorem openCellPoint_val (a : ℝˣ) (x : ℝ) :
    (weylLong 2 ℝ * (unipotentCoordinate x).val * diagonalPoint a).val = !![0, 1; (a : ℝ), x] := by
  rw [Units.val_mul, Units.val_mul, weylLong_two_val, unipotentCoordinate_val, diagonalPoint_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotentCoordinate_phase (x : ℝ) :
    (Langlands.Whittaker.standardCharacter (realScaledCharacter (-1)) 1 (unipotentCoordinate x) : ℂ) =
      exp (((-2 * Real.pi * x : ℝ) : ℂ) * I) := by
  have h := unipotentCoordinate_entry x
  rw [Langlands.Whittaker.standardCharacter_apply, Fin.sum_univ_one]
  change (realScaledCharacter (-1)).complex ((unipotentCoordinate x).val.val 0 1) = _
  rw [h, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    realScaledCharacter_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The lowest compact-type coefficient in the ordinary real discrete-block model. -/
def discreteCoefficient (d : ComplexCharacterData) : G → ℂ :=
  additiveJacquetIntegral (-1) (blockTest d)

/-- The power of the positive diagonal entry in the discrete-block coefficient. -/
def diagonalExponent (d : ComplexCharacterData) : ℂ :=
  d.exponent + ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2

/-- The nonzero constant in the diagonal Jacquet formula at additive scale one. -/
def diagonalConstant (d : ComplexCharacterData) : ℂ :=
  (2 * I) ^ (d.weight.natAbs + 1) *
    ((2 * (Real.pi : ℂ)) ^ (d.weight.natAbs + 1) / (d.weight.natAbs.factorial : ℂ))

theorem diagonalConstant_ne_zero (d : ComplexCharacterData) : diagonalConstant d ≠ 0 := by
  have hπ : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn : (d.weight.natAbs.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold diagonalConstant
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero I_ne_zero))
    (div_ne_zero (pow_ne_zero _ hπ) hn)

theorem discreteCoefficient_mem (d : ComplexCharacterData) (hd : d.weight ≠ 0) :
    discreteCoefficient d ∈ realWhittakerModel 1 [.induced d] 1 := by
  have hDom : IsStrictlyDominant (realPositionExponent [.induced d]) 1 := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    have hn : 0 < |(d.weight : ℝ)| := abs_pos.mpr (by exact_mod_cast hd)
    simp only [realPositionExponent, add_re, sub_re]
    norm_num [Complex.div_re]
    linarith
  let f : Automorphic.realStandardKFinite 2 [.induced d] := ⟨blockTest d, blockTest_mem d⟩
  have h := realGodementOpenCellModel 1 [.induced d] (-1) hDom f
  apply RealUniformWhittaker.model_le_model
  simpa only [neg_neg, f, discreteCoefficient] using h

private theorem discreteCoefficient_of_sign (d : ComplexCharacterData) (hd : d.weight ≠ 0)
    (a : ℝˣ) (b r : ℝ) (hb : b = 1 ∨ b = -1) (hr : 0 < r) (ha : (a : ℝ) = b * r) :
    discreteCoefficient d (diagonalPoint a) =
      (2 * I) ^ (d.weight.natAbs + 1) * (r : ℂ) ^ diagonalExponent d *
        RealLowestWeightFourier.positiveExpPower r d.weight.natAbs b := by
  let n := d.weight.natAbs
  have hn : n ≠ 0 := (Int.natAbs_pos.mpr hd).ne'
  let f (x : ℝ) : ℂ := ((r : ℂ) - (x : ℂ) * I)⁻¹ ^ (n + 1)
  let A := (2 * I) ^ (n + 1) * (r : ℂ) ^ diagonalExponent d
  let F (x : ℝ) := f (b * x)
  have hFourier : 𝓕 f = RealLowestWeightFourier.positiveExpPower r n :=
    (RealLowestWeightFourier.realLowestWeightFourier r hr n hn).2
  have hFB : 𝓕 F 1 = 𝓕 f b := by
    rcases hb with rfl | rfl
    · simp only [F, one_mul]
    · change 𝓕 (fun x : ℝ => f (-1 * x)) 1 = _
      simp only [neg_mul, one_mul]
      rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]
  have hk (x : ℝ) : additiveJacquetKernel (-1) (blockTest d) (diagonalPoint a) (unipotentCoordinate x) =
      A * (exp (((-2 * Real.pi * x : ℝ) : ℂ) * I) * F x) := by
    unfold additiveJacquetKernel
    rw [unipotentCoordinate_phase,
      blockTest_openCell d b r x hb hr _ ((openCellPoint_val a x).trans (by rw [ha]))]
    simp only [A, F, f, diagonalExponent, Complex.ofReal_mul]
    ring
  rw [discreteCoefficient, additiveJacquetIntegral,
    ← unipotentCoordinate_measurePreserving.integral_comp unipotentCoordinate.measurableEmbedding]
  simp_rw [hk, integral_const_mul]
  have hI : (∫ x : ℝ, exp (((-2 * Real.pi * x : ℝ) : ℂ) * I) * F x) = 𝓕 F 1 := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_one, smul_eq_mul]
  rw [hI, hFB, hFourier]

/-- A real discrete block has an actual ordinary coefficient supported on the
positive half of the first diagonal, with a single exponential there. -/
def RealDiscreteRankTwoWhittakerStatement : Prop :=
  ∀ (d : ComplexCharacterData), d.weight ≠ 0 →
    discreteCoefficient d ∈ realWhittakerModel 1 [.induced d] 1 ∧
    ∀ a : ℝˣ, discreteCoefficient d (diagonalPoint a) =
      if 0 < (a : ℝ) then diagonalConstant d * ((a : ℝ) : ℂ) ^ diagonalExponent d *
        exp (-((2 * Real.pi * (a : ℝ) : ℝ) : ℂ)) else 0

theorem realDiscreteRankTwoWhittaker : RealDiscreteRankTwoWhittakerStatement := by
  intro d hd
  refine ⟨discreteCoefficient_mem d hd, fun a => ?_⟩
  by_cases ha : 0 < (a : ℝ)
  · rw [ite_eq_left ha, discreteCoefficient_of_sign d hd a 1 (a : ℝ) (Or.inl rfl) ha (by simp)]
    simp only [RealLowestWeightFourier.positiveExpPower, max_eq_left zero_le_one, ofReal_one,
      one_pow, mul_one, diagonalConstant]
    ring
  · rw [ite_eq_right ha, discreteCoefficient_of_sign d hd a (-1) (-(a : ℝ)) (Or.inr rfl)
      (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt ha) a.ne_zero)) (by ring)]
    have hn : d.weight.natAbs ≠ 0 := (Int.natAbs_pos.mpr hd).ne'
    simp [RealLowestWeightFourier.positiveExpPower, zero_pow hn]

end Langlands.Global.RankinSelbergGlobal.RealDiscreteRankTwoWhittaker
