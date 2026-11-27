import Langlands.Global.RankinSelberg.RealGodementOpenCellModel
import Langlands.Global.RankinSelberg.RealLowestWeightFourier
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Global.RankinSelberg.RealDiscreteReciprocalFourier
import Langlands.Global.RankinSelberg.RealExactCharacterWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # The real rank-two discrete block on the diagonal -/

noncomputable section

open Complex Matrix MeasureTheory
open scoped FourierTransform Matrix Matrix.Norms.Operator ENNReal NNReal

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

private theorem unipotentCoordinate_measurePreserving_at (a : ℝˣ) :
    MeasurePreserving unipotentCoordinate (realSelfDualMeasure a).measure (upperStepHaar 1 a) := by
  have hμ := (measurePreserving_funUnique (realSelfDualMeasure a).measure (UpperEntryPair 2)).symm
  have hE : MeasurePreserving (upperEntryCoordinates 2 (K := ℝ)).symm
      (upperEntryProductMeasure (realSelfDualMeasure a) 2) (upperStepHaar 1 a) :=
    ⟨(upperEntryCoordinates 2 (K := ℝ)).symm.continuous.measurable, rfl⟩
  exact hE.comp hμ

private theorem unipotentCoordinate_measurePreserving :
    MeasurePreserving unipotentCoordinate volume (upperStepHaar 1 (-1)) := by
  have hV : (realSelfDualMeasure (-1)).measure = (volume : Measure ℝ) := by
    simp [realSelfDualMeasure, realScaledMeasure, realStandardMeasure,
      Langlands.HarmonicAnalysis.AdditiveHaarMeasure.scale]
  simpa only [hV] using unipotentCoordinate_measurePreserving_at (-1)

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

private theorem unipotentCoordinate_phase_at (a : ℝˣ) (x : ℝ) :
    (Langlands.Whittaker.standardCharacter (realScaledCharacter a) 1 (unipotentCoordinate x) : ℂ) =
      exp (((2 * Real.pi * x * (a : ℝ) : ℝ) : ℂ) * I) := by
  rw [Langlands.Whittaker.standardCharacter_apply, Fin.sum_univ_one]
  change (realScaledCharacter a).complex ((unipotentCoordinate x).val.val 0 1) = _
  rw [unipotentCoordinate_entry, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    realScaledCharacter_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem unipotentCoordinate_phase (x : ℝ) :
    (Langlands.Whittaker.standardCharacter (realScaledCharacter (-1)) 1 (unipotentCoordinate x) : ℂ) =
      exp (((-2 * Real.pi * x : ℝ) : ℂ) * I) := by
  simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one, neg_mul] using
    unipotentCoordinate_phase_at (-1) x

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

private theorem discrete_strictlyDominant (d : ComplexCharacterData) (hd : d.weight ≠ 0) :
    IsStrictlyDominant (realPositionExponent [.induced d]) 1 := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  have hn : 0 < |(d.weight : ℝ)| := abs_pos.mpr (by exact_mod_cast hd)
  simp only [realPositionExponent, add_re, sub_re]
  norm_num [Complex.div_re]
  linarith

theorem discreteCoefficient_mem (d : ComplexCharacterData) (hd : d.weight ≠ 0) :
    discreteCoefficient d ∈ realWhittakerModel 1 [.induced d] 1 := by
  have hDom := discrete_strictlyDominant d hd
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

/-! ## The bound for all compact-finite vectors -/

open RealDiscreteReciprocalFourier
open RealBlockFourierFinite RealBlockRotation RealBlockDerivative
open RealIwasawa
open scoped FourierTransform

local notation "K₂" => unitaryCompact ℝ 2
local notation "V(" d ")" => Automorphic.realStandardKFinite 2 [RealBlock.induced d]
local notation "E(" d ")" => GramFormula.shiftedExponent 2 (realPositionExponent [RealBlock.induced d])

private theorem standard_torus_unipotent (d : ComplexCharacterData) (f : V(d))
    (y : Fin 2 → ℝ) (u : Langlands.GeneralLinear.upperUnipotent 2 ℝ) (g : G) :
    f.val (torus y * u.val * g) = Complex.exp (∑ i, E(d) i * (y i : ℂ)) * f.val g := by
  have h := isExpEquivariant_of_mem_principalSeries
    (τ := fun i : Fin 2 => realPositionExponent [.induced d] i)
    (fun i x => InductionStages.realPositionCharacter_exp [.induced d] i x) f.2.1.1 y u g
  have hE : Langlands.Archimedean.matrixExpUnit 2 (Matrix.diagonal y) = torus y := by
    rw [RealPrincipalSeriesDuality.matrixExpUnit_diagonal]
    exact Units.ext rfl
  rw [hE] at h
  have he : (fun i : Fin 2 => realPositionExponent [.induced d] i +
      (((2 : ℕ) : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) = E(d) := by
    funext i
    unfold GramFormula.shiftedExponent
    ring
  rw [← he]
  exact h

private theorem blockRotation_weyl_arctan_val (x : ℝ) :
    (blockRotation 2 0 (Real.arctan x) * weylLong 2 ℝ).val =
      polarCompact 1 1 x (Real.sqrt (1 + x ^ 2)) := by
  rw [Units.val_mul, weylLong_two_val, blockRotation_val_eq (by decide : 0 + 1 < 2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, blockProj, rotationGenerator_eq (by decide : 0 + 1 < 2), ia, ib, polarCompact,
      Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_two,
      Real.sin_arctan, Real.cos_arctan, neg_div]

private theorem rankTwo_openCell_factor (x : ℝ) :
    weylLong 2 ℝ * (unipotentCoordinate x).val =
      torus ![-Real.log (Real.sqrt (1 + x ^ 2)), Real.log (Real.sqrt (1 + x ^ 2))] *
        (unipotentCoordinate x).val * (blockRotation 2 0 (Real.arctan x) * weylLong 2 ℝ) := by
  let ρ := Real.sqrt (1 + x ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  apply Units.ext
  rw [Units.val_mul, weylLong_two_val, unipotentCoordinate_val,
    Units.val_mul, Units.val_mul, torus_val, blockRotation_weyl_arctan_val, unipotentCoordinate_val]
  have hB : Matrix.diagonal (fun i => Real.exp ((![-Real.log ρ, Real.log ρ] : Fin 2 → ℝ) i)) *
      (!![1, x; 0, 1] : Mat) = polarUpper 1 x ρ := by
    ext i j
    rw [Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [polarUpper, Real.exp_neg, Real.exp_log hρ, div_eq_mul_inv, mul_comm]
  have hsq : ρ ^ 2 = 1 ^ 2 + x ^ 2 := by
    simpa [ρ] using Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  rw [hB, polarUpper_mul_compact 1 1 x ρ hρ.ne' hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- On the Jacquet cell `w₂n(x)`, the inducing vector separates into a radial factor
and a compact rotation profile. -/
private theorem discreteOpenCell_eq_angular (d : ComplexCharacterData) (f : V(d)) (x : ℝ) (g : G) :
    f.val (weylLong 2 ℝ * (unipotentCoordinate x).val * g) =
      ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)⁻¹ ^ (d.weight.natAbs + 1) *
        f.val (blockRotation 2 0 (Real.arctan x) * (weylLong 2 ℝ * g)) := by
  let ρ := Real.sqrt (1 + x ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have he : weylLong 2 ℝ * (unipotentCoordinate x).val * g =
      torus ![-Real.log ρ, Real.log ρ] * (unipotentCoordinate x).val *
        (blockRotation 2 0 (Real.arctan x) * (weylLong 2 ℝ * g)) := by
    rw [rankTwo_openCell_factor]
    simp only [ρ, mul_assoc]
  rw [he, standard_torus_unipotent, Fin.sum_univ_two, shiftedExponent_induced_zero, shiftedExponent_induced_one]
  change Complex.exp ((d.exponent + ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2) * (↑(-Real.log ρ)) +
    (d.exponent - ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2) * ↑(Real.log ρ)) * _ = _
  have h : (d.exponent + ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2) * (↑(-Real.log ρ)) +
      (d.exponent - ((d.weight.natAbs + 1 : ℕ) : ℂ) / 2) * ↑(Real.log ρ) =
      (-(d.weight.natAbs + 1 : ℕ) : ℂ) * (Real.log ρ : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_log hρ.le, mul_comm (-(d.weight.natAbs + 1 : ℕ) : ℂ), ← Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hρ.ne'), Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

private def permitted (k : ℕ) (j : ℤ) : Prop :=
  ∃ m : ℕ, j = ((k + 1 + 2 * m : ℕ) : ℤ) ∨ j = -((k + 1 + 2 * m : ℕ) : ℤ)

private theorem permitted_of_coeff_ne_zero (d : ComplexCharacterData) (f : V(d))
    {j : ℤ} {g : G} (hj : blockFourierCoefficient 2 0 j f.val g ≠ 0) :
    permitted d.weight.natAbs j := by
  have h := f.2.1.2 0 d rfl j
  have hweight' : |d.weight| ≤ |j| := le_of_not_gt fun hlt => hj (h hlt g)
  have hweight : (d.weight.natAbs : ℤ) ≤ |j| := by simpa only [Int.abs_eq_natAbs d.weight] using hweight'
  have hparity : Even (j - ((d.weight.natAbs : ℤ) + 1)) := by
    by_contra! he
    apply hj
    have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
        realPositionCharacter [.induced d] 0 (-1) * realPositionCharacter [.induced d] 1 (-1) := by
      change _ = realInducedFirstCharacter d (-1) * realInducedSecondCharacter d (-1)
      rw [InductionStages.realInducedFirstCharacter_neg_one, InductionStages.realInducedSecondCharacter_neg_one,
        mul_one]
      norm_cast
    exact RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even (by decide : 0 + 1 < 2) hpar f he g
  obtain ⟨l, hl⟩ := hparity
  by_cases hsign : 0 ≤ j
  · rw [abs_of_nonneg hsign] at hweight
    have hl₀ : 0 ≤ l := by omega
    refine ⟨l.toNat, Or.inl ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Int.toNat_of_nonneg hl₀]
    omega
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hweight
    have hl₀ : 0 ≤ -(d.weight.natAbs : ℤ) - 1 - l := by omega
    refine ⟨(-(d.weight.natAbs : ℤ) - 1 - l).toNat, Or.inr ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Int.toNat_of_nonneg hl₀]
    omega

private theorem norm_blockCoeff_le (f : G → ℂ) {A : ℝ}
    (hA : ∀ k ∈ K₂, ‖f k‖ ≤ A) (j : ℤ) {g : G} (hg : g ∈ K₂) :
    ‖blockFourierCoefficient 2 0 j f g‖ ≤ 2 * Real.pi * A := by
  rw [blockFourierCoefficient_eq_coeff, coeff]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := A) ?_).trans
  · rw [sub_zero, abs_of_nonneg (by positivity), mul_comm]
  · intro θ _
    have hφ : ‖Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    rw [norm_mul, hφ, mul_one]
    exact hA _ ((unitaryCompact ℝ 2).mul_mem (blockRotation_mem_unitaryCompact _ _ _) hg)

private def cellProfile (f : G → ℂ) (g : G) (x : ℝ) : ℂ :=
  f (weylLong 2 ℝ * (unipotentCoordinate x).val * g)

private theorem discrete_fourier_profile_bound (d : ComplexCharacterData) (hd : d.weight ≠ 0) (f : V(d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K₂, ∀ s : ℝ,
      ‖𝓕 (cellProfile f.val g) s‖ ≤ C * |s| ^ ((d.weight.natAbs : ℝ) / 2) := by
  classical
  let w := weylLong 2 ℝ
  let k := d.weight.natAbs
  let η := (k : ℝ) / 2
  have hk : k ≠ 0 := (Int.natAbs_pos.mpr hd).ne'
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηk : η ≤ k := by dsimp [η]; exact half_le_self (Nat.cast_nonneg _)
  have hw : w ∈ K₂ := RealEqualDualConvergence.weylLong_mem_unitary (r := 1)
  have hFc : Continuous f.val := f.2.1.1.1.continuous
  obtain ⟨D, _, hD⟩ := exists_eq_sum_blockFourierCoefficient (by decide : 0 + 1 < 2) hFc f.2.2
  obtain ⟨A, hA⟩ := exists_bound_unitaryCompact hFc
  let I := Finset.Icc (-(D : ℤ)) D
  let J := I.filter (permitted k)
  have hKern (j : J) : Integrable (angularKernel k j.val) ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℝ, ‖𝓕 (angularKernel k j.val) s‖ ≤ B * |s| ^ η :=
    realDiscreteAngularFourierBound k hk j.val (Finset.mem_filter.mp j.2).2 η hη hηk
  choose B hB hBF using fun j : J => (hKern j).2
  have hSumBound : 0 ≤ ∑ j : J, B j := Finset.sum_nonneg fun j _ => hB j
  refine ⟨max A 0 * (∑ j : J, B j), mul_nonneg (le_max_right _ _) hSumBound, fun g hg s => ?_⟩
  let coeff (j : ℤ) := (2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient 2 0 j f.val (w * g)
  have hcoeff (j : ℤ) : ‖coeff j‖ ≤ max A 0 := by
    have h := norm_blockCoeff_le f.val (A := max A 0) (fun q hq => (hA q hq).trans (le_max_left _ _)) j
      ((unitaryCompact ℝ 2).mul_mem hw hg)
    change ‖(2 * (Real.pi : ℂ))⁻¹ * _‖ ≤ _
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    exact (inv_mul_le_iff₀ (by positivity)).2 h
  have hEq : cellProfile f.val g = fun x => ∑ j : J, coeff j.val * angularKernel k j.val x := by
    funext x
    change f.val (w * (unipotentCoordinate x).val * g) = _
    rw [discreteOpenCell_eq_angular]
    rw [hD (w * g) ((unitaryCompact ℝ 2).mul_mem hw hg)]
    rw [← show (∑ j ∈ J, coeff j * angularKernel k j x) =
      ∑ j : J, coeff j.val * angularKernel k j.val x by
        exact (Finset.sum_coe_sort J (fun j => coeff j * angularKernel k j x)).symm]
    unfold angularKernel coeff
    have hSum : (∑ j ∈ I, blockFourierCoefficient 2 0 j f.val (w * g) * expMode j (Real.arctan x)) =
        ∑ j ∈ J, blockFourierCoefficient 2 0 j f.val (w * g) * expMode j (Real.arctan x) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnj
      have hnot : ¬ permitted k j := fun hyes => hnj (Finset.mem_filter.mpr ⟨hj, hyes⟩)
      have h0 : blockFourierCoefficient 2 0 j f.val (w * g) = 0 := by
        by_contra h0
        exact hnot (permitted_of_coeff_ne_zero d f h0)
      rw [h0, zero_mul]
    rw [hSum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hFourier : 𝓕 (cellProfile f.val g) s = ∑ j : J, coeff j.val * 𝓕 (angularKernel k j.val) s := by
    rw [hEq]
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    · intro j _
      have hInt := (hKern j).1.const_mul (coeff j.val)
      apply (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) s).2 at hInt
      simpa only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Real.inner_apply,
        mul_neg, neg_mul, mul_assoc] using hInt
  rw [hFourier]
  calc
    _ ≤ ∑ j : J, ‖coeff j.val * 𝓕 (angularKernel k j.val) s‖ := norm_sum_le _ _
    _ ≤ ∑ j : J, (max A 0 * B j) * |s| ^ η := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hcoeff j.val) (hBF j s) (norm_nonneg _) (le_max_right _ _)
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum, η, k]

private theorem additiveJacquetIntegral_eq_fourier (a : ℝˣ) (f : G → ℂ) (g : G) :
    additiveJacquetIntegral a f g =
      (((NNReal.sqrt ‖(a : ℝ)‖₊ : NNReal) : ℝ) : ℂ) * 𝓕 (cellProfile f g) (-(a : ℝ)) := by
  rw [additiveJacquetIntegral,
    ← (unipotentCoordinate_measurePreserving_at a).integral_comp unipotentCoordinate.measurableEmbedding]
  simp only [additiveJacquetKernel, unipotentCoordinate_phase_at]
  change (∫ x : ℝ, cellProfile f g x * exp (↑(2 * Real.pi * x * (a : ℝ)) * I)
      ∂((NNReal.sqrt ‖(a : ℝ)‖₊ : ℝ≥0∞) • volume)) = _
  rw [integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  change cellProfile f g x * exp (↑(2 * Real.pi * x * (a : ℝ)) * I) =
    exp (↑(-2 * Real.pi * x * -(a : ℝ)) * I) * cellProfile f g x
  rw [show -2 * Real.pi * x * -(a : ℝ) = 2 * Real.pi * x * (a : ℝ) from by ring, mul_comm]

private theorem torus_shear_rankTwo (y : Fin 2 → ℝ) (x : ℝ) (g : G) :
    weylLong 2 ℝ * (unipotentCoordinate (Real.exp (y 0 - y 1) * x)).val * (torus y * g) =
      torus ![y 1, y 0] * (weylLong 2 ℝ * (unipotentCoordinate x).val * g) := by
  rw [← mul_assoc (weylLong 2 ℝ * _ ) (torus y) g, ← mul_assoc (torus _) _ g]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, weylLong_two_val, unipotentCoordinate_val, torus_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Real.exp_sub]
  field_simp

private theorem cellProfile_fourier_torus (d : ComplexCharacterData) (f : V(d)) (y : Fin 2 → ℝ)
    (g : G) (q : ℝ) :
    𝓕 (cellProfile f.val (torus y * g)) q =
      (Real.exp (y 0 - y 1) : ℂ) *
        exp (E(d) 0 * (y 1 : ℂ) + E(d) 1 * (y 0 : ℂ)) *
        𝓕 (cellProfile f.val g) (Real.exp (y 0 - y 1) * q) := by
  let t := Real.exp (y 0 - y 1)
  have ht : 0 < t := Real.exp_pos _
  let b := exp (E(d) 0 * (y 1 : ℂ) + E(d) 1 * (y 0 : ℂ))
  have hOne (h : G) : f.val (torus ![y 1, y 0] * h) = b * f.val h := by
    have hEq := standard_torus_unipotent d f ![y 1, y 0] 1 h
    simpa only [OneMemClass.coe_one, mul_one, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, b] using hEq
  have hFunction (x : ℝ) : cellProfile f.val (torus y * g) x = b * cellProfile f.val g (t⁻¹ * x) := by
    have he := torus_shear_rankTwo y (t⁻¹ * x) g
    have hc : t * (t⁻¹ * x) = x := mul_inv_cancel_left₀ ht.ne' x
    change weylLong 2 ℝ * (unipotentCoordinate (t * (t⁻¹ * x))).val * (torus y * g) = _ at he
    rw [hc] at he
    exact congrArg f.val he |>.trans (hOne _)
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  let Q (x : ℝ) := exp (↑(-2 * Real.pi * x * (t * q)) * I) * cellProfile f.val g x
  have h (x : ℝ) : exp (↑(-2 * Real.pi * x * q) * I) * cellProfile f.val (torus y * g) x =
      b * Q (t⁻¹ * x) := by
    have he : -2 * Real.pi * (t⁻¹ * x) * (t * q) = -2 * Real.pi * x * q := by
      field_simp [show t ≠ 0 from ht.ne']
    rw [hFunction]
    dsimp only [Q]
    rw [he]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  change b * (∫ x : ℝ, Q (t⁻¹ * x)) = (t : ℂ) * b * ∫ x : ℝ, Q x
  rw [Measure.integral_comp_inv_mul_left, abs_of_pos ht, Complex.real_smul]
  ring

private theorem norm_torus_spherical_multiplier (d : ComplexCharacterData) (y : Fin 2 → ℝ) :
    ‖exp (E(d) 0 * (y 1 : ℂ) + E(d) 1 * (y 0 : ℂ))‖ =
      Real.exp (d.exponent.re * (y 0 + y 1) - ((d.weight.natAbs : ℝ) + 1) / 2 * (y 0 - y 1)) := by
  rw [Complex.norm_exp, shiftedExponent_induced_zero, shiftedExponent_induced_one]
  congr 1
  simp [Complex.mul_re]
  ring

/-- Absolute size of the Jacquet coefficient of any compact-finite vector in a single
real nonzero-weight induced block, after extracting the central twist. -/
def RealDiscreteOpenCellBoundStatement : Prop :=
  ∀ (d : ComplexCharacterData), d.weight ≠ 0 → ∀ (a : ℝˣ) (f : V(d)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin 2 → ℝ) (k : K₂),
      ‖additiveJacquetIntegral a f.val (torus y * k.val)‖ ≤
        C * Real.exp ((y 0 - y 1) / 2 + d.exponent.re * (y 0 + y 1))

theorem realDiscreteOpenCellBound : RealDiscreteOpenCellBoundStatement := by
  intro d hd a f
  obtain ⟨C, hC, hb⟩ := discrete_fourier_profile_bound d hd f
  let c : ℝ := (NNReal.sqrt ‖(a : ℝ)‖₊ : ℝ)
  let η := (d.weight.natAbs : ℝ) / 2
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  let A := c * C * |(a : ℝ)| ^ η
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hc hC) (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨A, hA, fun y k => ?_⟩
  let b := y 0 - y 1
  let u := d.exponent.re * (y 0 + y 1)
  let t := Real.exp b
  have ht : 0 < t := Real.exp_pos _
  rw [additiveJacquetIntegral_eq_fourier, cellProfile_fourier_torus, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc, Complex.norm_real, Real.norm_of_nonneg ht.le,
    norm_torus_spherical_multiplier]
  change c * (t * Real.exp (u - ((d.weight.natAbs : ℝ) + 1) / 2 * b) *
    ‖𝓕 (cellProfile f.val k.val) (t * -(a : ℝ))‖) ≤ _
  calc
    _ ≤ c * (t * Real.exp (u - ((d.weight.natAbs : ℝ) + 1) / 2 * b) *
        (C * |t * -(a : ℝ)| ^ η)) := by
      gcongr
      exact hb k.val k.property _
    _ = A * Real.exp (b / 2 + u) := by
      rw [abs_mul, abs_neg, abs_of_pos ht, Real.mul_rpow ht.le (abs_nonneg _)]
      dsimp only [t, A]
      rw [← Real.exp_mul]
      calc
        _ = (c * C * |(a : ℝ)| ^ η) * (Real.exp b * Real.exp (u - ((d.weight.natAbs : ℝ) + 1) / 2 * b) *
          Real.exp (b * η)) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          dsimp [η]
          ring

private theorem blockTest_fourier_nonzero (d : ComplexCharacterData) (hd : d.weight ≠ 0)
    (s : ℝˣ) (b : ℝ) (hs : (s : ℝ) = b) (hb : b = 1 ∨ b = -1) (q : ℝ) (hq : 0 < b * q) :
    𝓕 (cellProfile (blockTest d) (diagonalPoint s)) q ≠ 0 := by
  let n := d.weight.natAbs
  have hn : n ≠ 0 := (Int.natAbs_pos.mpr hd).ne'
  let A := (2 * Complex.I) ^ (n + 1)
  let f (x : ℝ) : ℂ := (1 - (x : ℂ) * Complex.I)⁻¹ ^ (n + 1)
  have hCell : cellProfile (blockTest d) (diagonalPoint s) = fun x => A * f (b * x) := by
    funext x
    have he := blockTest_openCell d b 1 x hb one_pos _
      ((openCellPoint_val s x).trans (by rw [hs, mul_one]))
    change cellProfile (blockTest d) (diagonalPoint s) x = _ at he
    simpa only [Complex.ofReal_one, one_cpow, mul_one, Complex.ofReal_mul, n, A, f] using he
  have hF : 𝓕 f = RealLowestWeightFourier.positiveExpPower 1 n := by
    simpa only [Complex.ofReal_one, f] using (RealLowestWeightFourier.realLowestWeightFourier 1 one_pos n hn).2
  have hReflection : 𝓕 (fun x => f (b * x)) q = 𝓕 f (b * q) := by
    rcases hb with rfl | rfl
    · simp only [one_mul]
    · simp only [neg_mul, one_mul]
      rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]
  have hScale : 𝓕 (fun x => A * f (b * x)) q = A * 𝓕 (fun x => f (b * x)) q := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    have h (x : ℝ) : exp (↑(-2 * Real.pi * x * q) * I) * (A * f (b * x)) =
        A * (exp (↑(-2 * Real.pi * x * q) * I) * f (b * x)) := by ring
    simp_rw [h, integral_const_mul]
  rw [hCell, hScale, hReflection, hF, RealLowestWeightFourier.positiveExpPower, max_eq_left hq.le]
  apply mul_ne_zero
  · exact pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact div_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) (by exact_mod_cast Nat.factorial_ne_zero n)
      · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq.ne')
    · exact Complex.exp_ne_zero _

private theorem additiveJacquetUniformLinear_discrete_ne_zero (d : ComplexCharacterData)
    (hd : d.weight ≠ 0) (a : ℝˣ) :
    additiveJacquetUniformLinear a (discrete_strictlyDominant d hd) ≠ 0 := by
  let f : V(d) := ⟨blockTest d, blockTest_mem d⟩
  have hnonzero : ∃ g : G, additiveJacquetIntegral a f.val g ≠ 0 := by
    let q : ℝ := -(a : ℝ)
    have hqat : q ≠ 0 := neg_ne_zero.mpr a.ne_zero
    have hq : ∃ (s : ℝˣ) (b : ℝ), (s : ℝ) = b ∧ (b = 1 ∨ b = -1) ∧ 0 < b * q := by
      rcases lt_or_gt_of_ne hqat with hneg | hpos
      · exact ⟨-1, -1, by simp, Or.inr rfl, by simpa using neg_pos.mpr hneg⟩
      · exact ⟨1, 1, by simp, Or.inl rfl, by simpa using hpos⟩
    obtain ⟨s, b, hs, hb, hpos⟩ := hq
    refine ⟨diagonalPoint s, ?_⟩
    rw [additiveJacquetIntegral_eq_fourier]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)).ne'))
      (blockTest_fourier_nonzero d hd s b hs hb q hpos)
  obtain ⟨g, hg⟩ := hnonzero
  intro h
  apply hg
  rw [← additiveJacquetUniformLinear_apply a (discrete_strictlyDominant d hd) f, h]
  rfl

private theorem discrete_whittaker_eq_jacquetRange (d : ComplexCharacterData) (hd : d.weight ≠ 0)
    (a : ℝˣ) :
    realWhittakerModel 1 [.induced d] (-a) =
      LinearMap.range (additiveJacquetUniformLinear a (discrete_strictlyDominant d hd)) := by
  let ds := [RealBlock.induced d]
  have hr : realRank ds = 2 := rfl
  let C := additiveJacquetUniformLinear a (discrete_strictlyDominant d hd)
  have hC : IsRealWhittakerIntertwiner 1 ds (-a) C :=
    (isRealUniformWhittakerIntertwiner_additiveJacquetUniformLinear a (discrete_strictlyDominant d hd)).1
  have hC₀ : C ≠ 0 := additiveJacquetUniformLinear_discrete_ne_zero d hd a
  obtain ⟨T, hTs, hT⟩ := RealPrincipalSeries.surjectiveIntertwiner_ascendingExpand 2 ds hr
  have hCt₀ : C.comp T ≠ 0 := by
    intro he
    apply hC₀
    ext1 f
    obtain ⟨v, rfl⟩ := hTs f
    exact LinearMap.congr_fun he v
  have hIncl : LinearMap.range C ≤ realWhittakerModel 1 ds (-a) :=
    le_iSup_of_le C (le_iSup_of_le hC le_rfl)
  apply le_antisymm ?_ hIncl
  refine iSup_le fun B => iSup_le fun hB => ?_
  obtain ⟨c, hc⟩ := RealPrincipalSeries.realExactCharacterWhittakerUniqueness 1
    (RealPrincipalSeries.ascendingCharacters ds) ((RealPrincipalSeries.realRank_ascendingExpand ds).trans hr)
    (-a) (B.comp T) (C.comp T) (RealPrincipalSeries.isRealWhittakerIntertwiner_pullback hT hB)
    (RealPrincipalSeries.isRealWhittakerIntertwiner_pullback hT hC) hCt₀
  rintro W ⟨f, rfl⟩
  obtain ⟨v, rfl⟩ := hTs f
  exact ⟨c • T v, (C.map_smul c (T v)).trans (LinearMap.congr_fun hc v).symm⟩

/-- The exact Whittaker coefficient model of a single real nonzero-weight induced block
has a half-modulus bound with the real determinant twist extracted. -/
def RealDiscreteWhittakerBoundStatement : Prop :=
  ∀ (d : ComplexCharacterData), d.weight ≠ 0 → ∀ (a : ℝˣ) (W : G → ℂ),
    W ∈ realWhittakerModel 1 [.induced d] a →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin 2 → ℝ) (k : K₂),
      ‖W (torus y * k.val)‖ ≤ C * Real.exp ((y 0 - y 1) / 2 + d.exponent.re * (y 0 + y 1))

theorem realDiscreteWhittakerBound : RealDiscreteWhittakerBoundStatement := by
  intro d hd a W hW
  have h := discrete_whittaker_eq_jacquetRange d hd (-a)
  rw [neg_neg] at h
  rw [h] at hW
  obtain ⟨f, rfl⟩ := hW
  rw [additiveJacquetUniformLinear_apply]
  exact realDiscreteOpenCellBound d hd (-a) f

end Langlands.Global.RankinSelbergGlobal.RealDiscreteRankTwoWhittaker
