import Langlands.Representation.Archimedean.ComplexUnitarySwapIntegral
import Langlands.Representation.Archimedean.ComplexGLTwoKFinite
import Langlands.Representation.Archimedean.ComplexGLTwoNoncompactPicture

/-! Compact evaluation of the adjacent-swap chart. -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

open ComplexBlock GLTwoModel GLTwoKFinite

/-- The squared norm of the bottom row of the rank-one chart. -/
def chartNormSq (z : ℂ) : ℝ := 1 + ‖z‖ ^ 2

def chartRadius (z : ℂ) : ℝ := Real.sqrt (chartNormSq z)

theorem chartRadius_pos (z : ℂ) : 0 < chartRadius z :=
  Real.sqrt_pos.2 (by unfold chartNormSq; positivity)

theorem chartRadius_sq (z : ℂ) : chartRadius z ^ 2 = chartNormSq z :=
  Real.sq_sqrt (by unfold chartNormSq; positivity)

private def chartBottom (z : ℂ) : Fin 2 → ℂ := ![1, z]

private def chartUnitRow (z : ℂ) : Fin 2 → ℂ := (((chartRadius z)⁻¹ : ℝ) : ℂ) • chartBottom z

private theorem chartUnitRow_nrm (z : ℂ) : nrm (chartUnitRow z) = 1 := by
  change nrm ((((chartRadius z)⁻¹ : ℝ) : ℂ) • chartBottom z) = _
  have hn : nrm (chartBottom z) = chartNormSq z := by simp [nrm, chartBottom, chartNormSq]
  rw [nrm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (chartRadius_pos z).le),
    inv_pow, chartRadius_sq, hn, inv_mul_cancel₀]
  unfold chartNormSq
  positivity

/-- The determinant-one unitary matrix whose bottom row is `[1,z]` divided by its norm. -/
def chartCompact (z : ℂ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  kU (chartUnitRow z) (chartUnitRow_nrm z)

theorem chartCompact_det (z : ℂ) : ((chartCompact z : Matrix (Fin 2) (Fin 2) ℂ)).det = 1 := by
  change (bottomMat (chartUnitRow z)).det = _
  rw [det_bottomMat, chartUnitRow_nrm, Complex.ofReal_one]

theorem chartCompact_val (z : ℂ) : (chartCompact z : Matrix (Fin 2) (Fin 2) ℂ) =
    !![starRingEnd ℂ z / (chartRadius z : ℂ), -1 / (chartRadius z : ℂ);
      1 / (chartRadius z : ℂ), z / (chartRadius z : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartCompact, kU, bottomMat, chartUnitRow, chartBottom, Complex.ofReal_inv,
      div_eq_mul_inv, mul_comm]

/-- The radial factor from the two diagonal entries of the upper-triangular factor. -/
def swapRadial (D : ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((-D - 1) * (Real.log (chartNormSq z) : ℂ))

/-- The chart normalized by dividing its bottom row by its norm. -/
private theorem eval_wn {d e : ComplexCharacterData} {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (hf : f ∈ complexStandardModule 2 [d, e]) (z : ℂ) :
    f (ComplexGLTwoNoncompact.wn z) = (-1 : ℂ) ^ d.weight *
      swapRadial (d.exponent - e.exponent) z * f (Unitary.toUnits (chartCompact z)) := by
  let R : ℝ := chartRadius z
  have hR : 0 < R := chartRadius_pos z
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  let a : Fin 2 → ℂˣ :=
    ![Units.mk0 ((-1 : ℂ) / R) (div_ne_zero (by norm_num) hRc), Units.mk0 (R : ℂ) hRc]
  let k := Unitary.toUnits (chartCompact z)
  have hrow : row (↑(Iwasawa.diagonalUnits a * k) : Matrix (Fin 2) (Fin 2) ℂ) =
      row (↑(ComplexGLTwoNoncompact.wn z) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [row_diag_mul, ComplexGLTwoNoncompact.wn_val]
    change (a 1 : ℂ) • row (bottomMat (chartUnitRow z)) = _
    rw [row_bottomMat]
    have ha : (a 1 : ℂ) = R := rfl
    rw [ha]
    change (R : ℂ) • ((↑(R⁻¹ : ℝ) : ℂ) • chartBottom z) = row !![0, 1; 1, z]
    rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hRc, one_smul]
    funext j
    fin_cases j <;> rfl
  have hdet : (↑(Iwasawa.diagonalUnits a * k) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (↑(ComplexGLTwoNoncompact.wn z) : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [det_diag_mul, ComplexGLTwoNoncompact.wn_val]
    change (-(1 : ℂ) / R) * (R : ℂ) * (↑(chartCompact z) : Matrix (Fin 2) (Fin 2) ℂ).det = _
    rw [chartCompact_det]
    simp [Matrix.det_fin_two, hRc]
  rw [eq_of_row_det hf hrow.symm hdet.symm, diag_mul_apply hf]
  have ha0 : (a 0 : ℂ) = (-1 : ℂ) * ((R⁻¹ : ℝ) : ℂ) := by
    change (-1 : ℂ) / (R : ℂ) = _
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  have ha1 : (a 1 : ℂ) = R := rfl
  have hInvR : 0 < R⁻¹ := inv_pos.2 hR
  rw [ha0, ha1, unitChar_mul _ _ (by norm_num) (Complex.ofReal_ne_zero.mpr hInvR.ne'),
    unitChar_of_norm_eq_one _ _ (by simp), unitChar_ofReal _ _ hInvR, unitChar_ofReal _ _ hR,
    mul_assoc ((-1 : ℂ) ^ d.weight), ← Complex.exp_add, Real.log_inv]
  congr 2
  unfold swapRadial
  congr 1
  rw [← chartRadius_sq, Real.log_pow]
  push_cast
  dsimp [R]
  ring

/-- The compact unitary factor inserted in the two adjacent rows of the full group. -/
theorem eval_block_chart {n : ℕ} {pre post : List ComplexCharacterData} {d e : ComplexCharacterData}
    (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p)
    (v : KFs n (pre ++ d :: e :: post)) (k : Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) :
    (v : Langlands.GeneralLinear n ℂ → ℂ) (block p hp (ComplexGLTwoNoncompact.wn z) * Unitary.toUnits k) =
      (-1 : ℂ) ^ d.weight * swapRadial (d.exponent - e.exponent) z *
        (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits (blockU p hp (chartCompact z) * k)) := by
  let w := complexStandardRep n (pre ++ d :: e :: post) k v
  have hw := eval_wn (res p hp pre post d e hpre w).2.1 z
  simp only [res_apply, w, principalSeriesRep_apply_coe, TranslateFinite.rightTranslation_apply,
    block_toUnits, ← map_mul, twist_exponent_sub] at hw
  simpa only [ComplexBlock.twist, characterOfParams_weight] using hw

end Langlands.Archimedean.ComplexUnitary
