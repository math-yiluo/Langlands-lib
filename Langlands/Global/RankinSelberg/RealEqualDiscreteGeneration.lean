import Langlands.Analysis.SchwartzGaussian
import Langlands.Global.RankinSelberg.RealDiscreteRankTwoAngular
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.RealIwasawaQuotientHaar
import Langlands.Global.RankinSelberg.RealLocalUniformCentralCharacter
import Langlands.Global.RankinSelberg.RealOrdinaryCharacterTransport
import Langlands.Global.RankinSelberg.RealWhittakerUniformDerivativeGrowth
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages

/-! # Real equal-rank normalized tests for two discrete blocks -/

noncomputable section

open Complex MeasureTheory MeasureTheory.Measure Matrix Set
open scoped ContDiff ENNReal NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace Langlands.Global.RankinSelbergGlobal.RealEqualDiscreteGeneration

open ArchimedeanLocal RealDiscreteRankTwoWhittaker RealDiscreteRankTwoAngular
open RealEqualConvergence (logDet logDet_torus_mul lastRow_torus_mul kRow kernel)
open RealIwasawa (torus torus_val)
open RealIwasawaQuotientHaar (quotientChart measurable_quotientChart
  logDiagonalMeasure rootModulus realIwasawaQuotientHaar)
open Langlands.Archimedean Langlands.Archimedean.RealSmallOrthogonalHaar
open Langlands.Archimedean.RealPrincipalSeriesDuality (ofReal_exp_cpow)
open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)
open Langlands.GodementJacquet (tateScalarEquiv)
open RealRankZero (det_val_tateScalarEquiv)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel RealPrincipalSeriesDuality.measurableSpaceK
attribute [local instance 100] LieRing.ofAssociativeRing

local instance (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

local notation "G" => Langlands.GeneralLinear 2 ℝ
local notation "O₂" => Matrix.unitaryGroup (Fin 2) ℝ
local notation "K₂" => unitaryCompact ℝ 2
local notation "Row" => Fin 2 → ℝ
local notation "row" => Langlands.RankinSelberg.lastRow (n := 1)
local notation "rot" => fun t => Unitary.toUnits (rotation t)
local notation "R" => Unitary.toUnits reflectTwo

private abbrev absWeight (d : ComplexCharacterData) : ℕ := d.weight.natAbs

private def weightGap (d e : ComplexCharacterData) : ℕ :=
  max (absWeight d) (absWeight e) - min (absWeight d) (absWeight e)

private def zSum (d e : ComplexCharacterData) (s : ℂ) : ℂ :=
  s + d.exponent + e.exponent + ((absWeight d : ℂ) + (absWeight e : ℂ)) / 2

private def zGap (d e : ComplexCharacterData) (s : ℂ) : ℂ :=
  s + d.exponent + e.exponent + (weightGap d e : ℂ) / 2

private theorem zGap_sub_zSum (d e : ComplexCharacterData) (s : ℂ) :
    zGap d e s - zSum d e s = -((min (absWeight d) (absWeight e) : ℕ) : ℂ) := by
  unfold zGap zSum weightGap
  rcases le_total (absWeight d) (absWeight e) with h | h
  · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h]
    ring
  · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h]
    ring

private theorem abs_sum_gap (m n : ℤ) :
    ((m + n).natAbs = m.natAbs + n.natAbs ∧
      (m - n).natAbs = max m.natAbs n.natAbs - min m.natAbs n.natAbs) ∨
    ((m - n).natAbs = m.natAbs + n.natAbs ∧
      (m + n).natAbs = max m.natAbs n.natAbs - min m.natAbs n.natAbs) := by
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;>
    rcases le_total m.natAbs n.natAbs with h | h <;>
    simp only [max_eq_right, min_eq_left, max_eq_left, min_eq_right, h] <;> omega

private theorem pairFactor_eq (d e : ComplexCharacterData) (s : ℂ) :
    ((realPairLFactor [.induced d] [.induced e]).denominator s)⁻¹ =
      Gammaℂ (zSum d e s) * Gammaℂ (zGap d e s) := by
  change ((realLFactor [.induced (d.mul e), .induced (d.mul e.conj)]).denominator s)⁻¹ = _
  rw [realLFactor_cons, realLFactor_singleton, RealBlock.lFactor_induced, RealBlock.lFactor_induced,
    ReciprocalEntire.denominator_mul, ReciprocalEntire.denominator_shift, ReciprocalEntire.denominator_shift]
  change (((Gammaℂ (s + ((d.exponent + e.exponent) + (((d.weight + e.weight).natAbs : ℂ) / 2))))⁻¹ *
    (Gammaℂ (s + ((d.exponent + e.exponent) + (((d.weight + -e.weight).natAbs : ℂ) / 2))))⁻¹)⁻¹) = _
  rw [_root_.mul_inv_rev, inv_inv, inv_inv, ← sub_eq_add_neg]
  rcases abs_sum_gap d.weight e.weight with h | h
  · rw [h.1, h.2, Nat.cast_add, mul_comm, zSum, zGap, weightGap]
    congr 2 <;> ring
  · rw [h.1, h.2, Nat.cast_add, zSum, zGap, weightGap]
    congr 2 <;> ring

private def scaledEuclideanRow : Row ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((WithLp.linearEquiv 2 ℝ Row).symm.trans
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 2)) (Real.sqrt Real.pi)
      (Real.sqrt_pos.mpr Real.pi_pos).ne')).toContinuousLinearEquiv

private def rowGaussian : 𝓢(Row, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ scaledEuclideanRow
    (ComplexGodementGaussianPolynomial.radialGaussian.postcompCLM Complex.ofRealCLM)

private theorem rowGaussian_apply (x : Row) :
    rowGaussian x = (Real.exp (-(Real.pi * (x 0 ^ 2 + x 1 ^ 2))) : ℂ) := by
  change (Real.exp (-‖Real.sqrt Real.pi • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) : ℂ) = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt Real.pi_pos.le, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  change (Real.exp (-(Real.pi * (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2))) : ℂ) = _
  simp only [Real.norm_eq_abs, sq_abs]

private def angularMonomial (d e : ComplexCharacterData) (x : Row) : ℂ :=
  if absWeight e ≤ absWeight d then ((x 1 : ℂ) + I * (x 0 : ℂ)) ^ weightGap d e
  else ((x 1 : ℂ) - I * (x 0 : ℂ)) ^ weightGap d e

private def rowCoordinate (i : Fin 2) : Row →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

private theorem angularMonomial_temperate (d e : ComplexCharacterData) :
    (angularMonomial d e).HasTemperateGrowth := by
  have hI := (Function.HasTemperateGrowth.const (E := Row) I).mul (rowCoordinate 0).hasTemperateGrowth
  by_cases h : absWeight e ≤ absWeight d
  · change (fun x : Row => if absWeight e ≤ absWeight d then _ else _).HasTemperateGrowth
    simp only [ite_eq_left h]
    change (fun x : Row => (rowCoordinate 1 x + I * rowCoordinate 0 x) ^ weightGap d e).HasTemperateGrowth
    exact ((rowCoordinate 1).hasTemperateGrowth.add hI).pow _
  · change (fun x : Row => if absWeight e ≤ absWeight d then _ else _).HasTemperateGrowth
    simp only [ite_eq_right h]
    change (fun x : Row => (rowCoordinate 1 x - I * rowCoordinate 0 x) ^ weightGap d e).HasTemperateGrowth
    exact ((rowCoordinate 1).hasTemperateGrowth.sub hI).pow _

private def rowTest (d e : ComplexCharacterData) : 𝓢(Row, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (angularMonomial d e) rowGaussian

private theorem rowTest_apply (d e : ComplexCharacterData) (x : Row) :
    rowTest d e x = angularMonomial d e x * (Real.exp (-(Real.pi * (x 0 ^ 2 + x 1 ^ 2))) : ℂ) := by
  rw [rowTest, SchwartzMap.smulLeftCLM_apply_apply (angularMonomial_temperate d e),
    smul_eq_mul, rowGaussian_apply]

private theorem angularCharacter_mul (θ : ℝ) : angularCharacter θ * angularCharacter (-θ) = 1 := by
  have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  unfold angularCharacter
  rw [Real.cos_neg, Real.sin_neg, ofReal_neg]
  linear_combination h - (Real.sin θ : ℂ) ^ 2 * Complex.I_sq

private theorem angularMonomial_cancel (d e : ComplexCharacterData) (t θ : ℝ) (x : Row)
    (hx₀ : x 0 = t * Real.sin θ) (hx₁ : x 1 = t * Real.cos θ) :
    angularCharacter θ ^ (absWeight d + 1) * angularCharacter (-θ) ^ (absWeight e + 1) *
      rowTest d e x = (t : ℂ) ^ weightGap d e * exp (-((Real.pi * t ^ 2 : ℝ) : ℂ)) := by
  have hRad : x 0 ^ 2 + x 1 ^ 2 = t ^ 2 := by
    rw [hx₀, hx₁]
    linear_combination t ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [rowTest_apply, hRad, ofReal_exp, ofReal_neg, angularMonomial, hx₀, hx₁]
  simp only [ofReal_mul]
  have hPlus : (t : ℂ) * (Real.cos θ : ℂ) + I * ((t : ℂ) * (Real.sin θ : ℂ)) =
      (t : ℂ) * angularCharacter (-θ) := by
    simp only [angularCharacter, Real.cos_neg, Real.sin_neg, ofReal_neg]
    ring
  have hMinus : (t : ℂ) * (Real.cos θ : ℂ) - I * ((t : ℂ) * (Real.sin θ : ℂ)) =
      (t : ℂ) * angularCharacter θ := by unfold angularCharacter; ring
  have hU := angularCharacter_mul θ
  by_cases h : absWeight e ≤ absWeight d
  · rw [ite_eq_left h, hPlus, mul_pow]
    have hGap : absWeight e + 1 + weightGap d e = absWeight d + 1 := by
      simp only [weightGap, max_eq_left h, min_eq_right h]; omega
    calc
      _ = (t : ℂ) ^ weightGap d e * exp (-((Real.pi * t ^ 2 : ℝ) : ℂ)) *
          (angularCharacter θ ^ (absWeight d + 1) *
            (angularCharacter (-θ) ^ (absWeight e + 1) * angularCharacter (-θ) ^ weightGap d e)) := by
          simp only [ofReal_mul]
          ring
      _ = _ := by rw [← pow_add, hGap, ← mul_pow, hU, one_pow, mul_one, ofReal_mul]
  · rw [ite_eq_right h, hMinus, mul_pow]
    have h' : absWeight d ≤ absWeight e := le_of_lt (lt_of_not_ge h)
    have hGap : absWeight d + 1 + weightGap d e = absWeight e + 1 := by
      simp only [weightGap, max_eq_right h', min_eq_left h']; omega
    calc
      _ = (t : ℂ) ^ weightGap d e * exp (-((Real.pi * t ^ 2 : ℝ) : ℂ)) *
          ((angularCharacter θ ^ (absWeight d + 1) * angularCharacter θ ^ weightGap d e) *
            angularCharacter (-θ) ^ (absWeight e + 1)) := by
          simp only [ofReal_mul]
          ring
      _ = _ := by rw [← pow_add, hGap, ← mul_pow, hU, one_pow, mul_one, ofReal_mul]

private def logMellin (c : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  exp ((x : ℂ) * z) * exp (-((c * Real.exp x : ℝ) : ℂ))

private theorem integral_logMellin (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : 0 < z.re) :
    ∫ x, logMellin c z x = (c : ℂ) ^ (-z) * Gamma z := by
  have h (x : ℝ) : logMellin c z x = Real.exp x •
      ((Real.exp x : ℂ) ^ (z - 1) * exp (-(c * Real.exp x))) := by
    rw [logMellin, Complex.real_smul, ← mul_assoc, ofReal_mul]
    congr 1
    calc
      _ = (Real.exp x : ℂ) ^ z := (ofReal_exp_cpow x z).symm
      _ = (Real.exp x : ℂ) ^ (1 + (z - 1)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (ofReal_ne_zero.mpr (Real.exp_ne_zero x)), cpow_one]
  simp_rw [h]
  rw [integral_comp_exp (fun x => (x : ℂ) ^ (z - 1) * exp (-(c * x))),
    integral_cpow_mul_exp_neg_mul_Ioi hz hc, one_div, inv_cpow_ofReal_nonneg hc.le, ← cpow_neg]

private theorem integral_logMellin_fourPi (z : ℂ) (hz : 0 < z.re) :
    ∫ x, logMellin (4 * Real.pi) z x = ((2 : ℂ) ^ (-z) / 2) * Gammaℂ z := by
  rw [integral_logMellin _ (by positivity) _ hz, Gammaℂ_def]
  have h : (2 : ℂ) * (2 * Real.pi) = (↑(4 * Real.pi) : ℂ) := by push_cast; ring
  have hp := mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ))
    (by positivity : 0 ≤ 2 * Real.pi) (-z)
  push_cast at hp
  rw [← h, hp]
  ring

private theorem integral_logMellin_pi_twice (z : ℂ) (hz : 0 < z.re) :
    ∫ x : ℝ, logMellin Real.pi z (2 * x) = ((2 : ℂ) ^ z / 4) * Gammaℂ z := by
  rw [Measure.integral_comp_mul_left, integral_logMellin _ Real.pi_pos _ hz, Gammaℂ_def,
    Complex.real_smul]
  have h : ((2 * (Real.pi : ℂ)) ^ (-z)) = (2 : ℂ) ^ (-z) * (Real.pi : ℂ) ^ (-z) := by
    exact_mod_cast mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ)) Real.pi_pos.le (-z)
  rw [h, show ((|((2 : ℝ))⁻¹| : ℝ) : ℂ) = 1 / 2 by norm_num]
  have h2 : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  symm
  calc
    _ = ((2 : ℂ) ^ z * (2 : ℂ) ^ (-z)) * (1 / 2 * ((Real.pi : ℂ) ^ (-z) * Gamma z)) := by ring
    _ = _ := by rw [h2, one_mul]

private def expUnit (x : ℝ) : ℝˣ := Units.mk0 (Real.exp x) (Real.exp_ne_zero x)

private theorem diagonalPoint_val (a : ℝˣ) : (diagonalPoint a).val = !![(a : ℝ), 0; 0, 1] := by
  have ha : (tateScalarEquiv ℝ a).val 0 0 = (a : ℝ) :=
    (Matrix.det_fin_one _).symm.trans (det_val_tateScalarEquiv a)
  ext i j
  rw [diagonalPoint, UnequalAnalytic.padGL_apply]
  fin_cases i <;> fin_cases j <;> norm_num [ha, Matrix.one_apply]

private theorem torus_mul_eq (y : Row) (k : G) :
    torus y * k = diagonalPoint (expUnit (y 0 - y 1)) * k * GeneralLinear.scalar (expUnit (y 1)) := by
  have h : torus y = diagonalPoint (expUnit (y 0 - y 1)) * GeneralLinear.scalar (expUnit (y 1)) := by
    apply Units.ext
    rw [torus_val, Units.val_mul, diagonalPoint_val, Matrix.GeneralLinearGroup.coe_scalar]
    change _ = _ * Matrix.diagonal (fun _ : Fin 2 => Real.exp (y 1))
    ext i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [expUnit, Real.exp_sub, Real.exp_ne_zero]
  rw [h, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc]

private theorem uniformCoefficient_mul_scalar {d : ComplexCharacterData} {a : ℝˣ} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel 1 [.induced d] a) (g : G) (x : ℝ) :
    W (g * GeneralLinear.scalar (expUnit x)) = exp ((x : ℂ) * (2 * d.exponent)) * W g := by
  rw [RealJacquet.realUniformWhittakerCentralCharacter 1 [.induced d] (by simp [realRank, RealBlock.rank])
    a W hW (expUnit x) g]
  congr 1
  simp only [RealJacquet.determinant, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change (d.realInducedDeterminant (expUnit x) : ℂ) = _
  have hx := Real.exp_pos x
  have hz : ((realToComplex (expUnit x) : ℂˣ) : ℂ) = (Real.exp x : ℂ) := rfl
  rw [ComplexCharacterData.coe_realInducedDeterminant, d.character_eq, hz]
  change (((Real.exp x / |Real.exp x| : ℝ) : ℂ) *
    (((Real.exp x : ℂ) / (‖(Real.exp x : ℂ)‖ : ℂ)) ^ d.weight *
      (‖(Real.exp x : ℂ)‖ : ℂ) ^ (2 * d.exponent))) = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, div_self hx.ne', ofReal_one,
    div_self (ofReal_ne_zero.mpr hx.ne'), _root_.one_zpow, one_mul, one_mul, ofReal_exp_cpow]

private def toralKernel (d e : ComplexCharacterData) (s : ℂ) (y : Row) (k : K₂) : ℂ :=
  kernel (discreteCoefficient d) (discreteOppositeCoefficient e) (rowTest d e) (torus y * k.val) *
    exp (s * (logDet (torus y * k.val) : ℂ))

private def radialKernel (d e : ComplexCharacterData) (s : ℂ) (y : Row) : ℂ :=
  (diagonalConstant d * diagonalConstant e) *
    (logMellin (4 * Real.pi) (zSum d e s + 1) (y 0 - y 1) * logMellin Real.pi (zGap d e s) (2 * y 1))

private def orthogonalCompact (k : O₂) : K₂ := RealPrincipalSeriesHilbert.orthogonalCompactEquiv 2 k

private theorem toralKernel_rotation {d e : ComplexCharacterData} (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hW : discreteCoefficient d ∈ realUniformWhittakerModel 1 [.induced d] 1)
    (hV : discreteOppositeCoefficient e ∈ realUniformWhittakerModel 1 [.induced e] (-1))
    (s : ℂ) (y : Row) (θ : ℝ) :
    toralKernel d e s y (orthogonalCompact (rotation θ)) = radialKernel d e s y := by
  let x := y 0 - y 1
  let t := y 1
  let a := expUnit x
  let A := angularCharacter θ ^ (absWeight d + 1)
  let B := angularCharacter (-θ) ^ (absWeight e + 1)
  let k := orthogonalCompact (rotation θ)
  have hk : k.val = rot θ := rfl
  have ha : 0 < (a : ℝ) := Real.exp_pos _
  have hDiag (b : ComplexCharacterData) (hb : b.weight ≠ 0) :
      discreteCoefficient b (diagonalPoint a) = diagonalConstant b *
        exp ((x : ℂ) * diagonalExponent b) * exp (-((2 * Real.pi * Real.exp x : ℝ) : ℂ)) := by
    rw [(realDiscreteRankTwoWhittaker b hb).2 a, ite_eq_left ha]
    change diagonalConstant b * (Real.exp x : ℂ) ^ diagonalExponent b * _ = _
    rw [ofReal_exp_cpow]
    rfl
  have hWk := (realDiscreteRankTwoAngular d hd).2 a θ |>.1
  have hVk := (realDiscreteRankTwoAngular e he).2 a θ |>.2.1
  have hRow₀ : row (torus y * k.val) 0 = Real.exp t * Real.sin θ := by
    rw [lastRow_torus_mul]
    change Real.exp t * k.val.val 1 0 = _
    rw [hk, show (rot θ).val = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] from rotation_val θ]
    rfl
  have hRow₁ : row (torus y * k.val) 1 = Real.exp t * Real.cos θ := by
    rw [lastRow_torus_mul]
    change Real.exp t * k.val.val 1 1 = _
    rw [hk, show (rot θ).val = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] from rotation_val θ]
    rfl
  have hAngle : A * B * rowTest d e (row (torus y * k.val)) =
      exp ((t : ℂ) * (weightGap d e : ℂ)) * exp (-((Real.pi * Real.exp (2 * t) : ℝ) : ℂ)) := by
    have hSquare : Real.exp t ^ 2 = Real.exp (2 * t) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [angularMonomial_cancel d e (Real.exp t) θ _ hRow₀ hRow₁, hSquare, ← cpow_natCast, ofReal_exp_cpow]
  have hExp :
      exp ((t : ℂ) * (2 * d.exponent)) * exp ((t : ℂ) * (2 * e.exponent)) *
        exp ((x : ℂ) * diagonalExponent d) * exp ((x : ℂ) * diagonalExponent e) *
        exp (s * ((y 0 + y 1 : ℝ) : ℂ)) * exp ((t : ℂ) * (weightGap d e : ℂ)) =
      exp ((x : ℂ) * (zSum d e s + 1)) * exp (((2 * t : ℝ) : ℂ) * zGap d e s) := by
    simp only [← exp_add, diagonalExponent, zSum, zGap, x, t, ofReal_sub, ofReal_add,
      ofReal_mul, ofReal_ofNat, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hDecay : exp (-((2 * Real.pi * Real.exp x : ℝ) : ℂ)) *
      exp (-((2 * Real.pi * Real.exp x : ℝ) : ℂ)) = exp (-((4 * Real.pi * Real.exp x : ℝ) : ℂ)) := by
    rw [← exp_add]
    push_cast
    congr 1
    ring
  unfold toralKernel kernel
  rw [logDet_torus_mul, Fin.sum_univ_two]
  change discreteCoefficient d (torus y * k.val) * discreteOppositeCoefficient e (torus y * k.val) *
    rowTest d e (row (torus y * k.val)) * exp (s * ((y 0 + y 1 : ℝ) : ℂ)) = _
  have hWd : discreteCoefficient d (torus y * k.val) =
      exp ((t : ℂ) * (2 * d.exponent)) * (A * discreteCoefficient d (diagonalPoint a)) := by
    rw [torus_mul_eq, uniformCoefficient_mul_scalar hW, hk, hWk]
  have hVe : discreteOppositeCoefficient e (torus y * k.val) =
      exp ((t : ℂ) * (2 * e.exponent)) * (B * discreteCoefficient e (diagonalPoint a)) := by
    rw [torus_mul_eq, uniformCoefficient_mul_scalar hV, hk, hVk]
  rw [hWd, hVe, hDiag d hd, hDiag e he]
  calc
    _ = (diagonalConstant d * diagonalConstant e) *
        ((exp ((t : ℂ) * (2 * d.exponent)) * exp ((t : ℂ) * (2 * e.exponent)) *
          exp ((x : ℂ) * diagonalExponent d) * exp ((x : ℂ) * diagonalExponent e) *
          exp (s * ((y 0 + y 1 : ℝ) : ℂ))) *
         (A * B * rowTest d e (row (torus y * k.val))) *
         (exp (-((2 * Real.pi * Real.exp x : ℝ) : ℂ)) * exp (-((2 * Real.pi * Real.exp x : ℝ) : ℂ)))) := by
          ring
    _ = _ := by
      rw [hAngle, hDecay]
      have h : (exp ((t : ℂ) * (2 * d.exponent)) * exp ((t : ℂ) * (2 * e.exponent)) *
          exp ((x : ℂ) * diagonalExponent d) * exp ((x : ℂ) * diagonalExponent e) *
          exp (s * ((y 0 + y 1 : ℝ) : ℂ))) *
          (exp ((t : ℂ) * (weightGap d e : ℂ)) * exp (-((Real.pi * Real.exp (2 * t) : ℝ) : ℂ))) =
          (exp ((x : ℂ) * (zSum d e s + 1)) * exp (((2 * t : ℝ) : ℂ) * zGap d e s)) *
            exp (-((Real.pi * Real.exp (2 * t) : ℝ) : ℂ)) := by rw [← mul_assoc, hExp]
      rw [h]
      unfold radialKernel logMellin
      change _ = (diagonalConstant d * diagonalConstant e) *
        ((exp ((x : ℂ) * (zSum d e s + 1)) * exp (-((4 * Real.pi * Real.exp x : ℝ) : ℂ))) *
          (exp (((2 * t : ℝ) : ℂ) * zGap d e s) * exp (-((Real.pi * Real.exp (2 * t) : ℝ) : ℂ))))
      ring

private theorem toralKernel_reflected {d e : ComplexCharacterData} (hd : d.weight ≠ 0)
    (hW : discreteCoefficient d ∈ realUniformWhittakerModel 1 [.induced d] 1) (s : ℂ) (y : Row) (θ : ℝ) :
    toralKernel d e s y (orthogonalCompact (rotation θ * reflectTwo)) = 0 := by
  let a := expUnit (y 0 - y 1)
  have ha : ¬ 0 < ((-a : ℝˣ) : ℝ) := not_lt.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
  have hk : (orthogonalCompact (rotation θ * reflectTwo)).val = rot θ * R :=
    Unitary.toUnits.map_mul _ _
  have hZero : discreteCoefficient d (torus y * (orthogonalCompact (rotation θ * reflectTwo)).val) = 0 := by
    rw [torus_mul_eq, uniformCoefficient_mul_scalar hW, hk, ← mul_assoc (diagonalPoint a),
      (realDiscreteRankTwoAngular d hd).2 a θ |>.2.2,
      (realDiscreteRankTwoWhittaker d hd).2 (-a), ite_eq_right ha, mul_zero, mul_zero]
  simp [toralKernel, kernel, hZero]

private def compactHaar : Measure K₂ :=
  (RealPrincipalSeriesHilbert.haarOrthogonal 2).map (RealPrincipalSeriesHilbert.orthogonalCompactEquiv 2)

private theorem compactHaar_isHaar : compactHaar.IsHaarMeasure :=
  Measure.isHaarMeasure_map_of_isFiniteMeasure _
    (RealPrincipalSeriesHilbert.orthogonalCompactEquiv 2).toMonoidHom
    RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv
    (RealPrincipalSeriesHilbert.orthogonalCompactEquiv 2).surjective

private theorem integral_toralKernel {d e : ComplexCharacterData} (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hW : discreteCoefficient d ∈ realUniformWhittakerModel 1 [.induced d] 1)
    (hV : discreteOppositeCoefficient e ∈ realUniformWhittakerModel 1 [.induced e] (-1))
    (s : ℂ) (y : Row) (hCont : Continuous (toralKernel d e s y)) :
    ∫ k, toralKernel d e s y k ∂compactHaar = radialKernel d e s y / 2 := by
  let f : C(O₂, ℂ) :=
    ⟨toralKernel d e s y ∘ orthogonalCompact, hCont.comp
      RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv⟩
  rw [compactHaar, integral_map RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv.measurable.aemeasurable
    hCont.aestronglyMeasurable]
  change (∫ k, f k ∂RealPrincipalSeriesHilbert.haarOrthogonal 2) = _
  rw [integral_orthogonal_two]
  have hrot (θ : ℝ) : f (rotation θ) = radialKernel d e s y :=
    toralKernel_rotation hd he hW hV s y θ
  have href (θ : ℝ) : f (rotation θ * reflectTwo) = 0 :=
    toralKernel_reflected hd hW s y θ
  simp_rw [hrot, href]
  simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_zero, add_zero]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

private local instance : Unique (Langlands.GeneralLinear.UpperEntryPair 2) where
  default := ⟨(0, 1), by decide⟩
  uniq := by
    rintro ⟨⟨i, j⟩, hij⟩
    apply Subtype.ext
    fin_cases i <;> fin_cases j
    · exact ((by decide : ¬ (0 : Fin 2) < 0) hij).elim
    · rfl
    · exact ((by decide : ¬ (1 : Fin 2) < 0) hij).elim
    · exact ((by decide : ¬ (1 : Fin 2) < 1) hij).elim

private theorem rootModulus_two (y : Row) :
    (rootModulus y : ℝ) = Real.exp (y 1 - y 0) := by
  rw [rootModulus, Fintype.prod_unique]
  exact Real.coe_toNNReal _ (Real.exp_pos _).le

private def logCoordinates : Row ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.piFinTwo fun _ => ℝ).trans
    { toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun p => (p.1 + p.2, p.2)
      left_inv := fun _ => Prod.ext (sub_add_cancel _ _) rfl
      right_inv := fun _ => Prod.ext (add_sub_cancel_right _ _) rfl
      measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
      measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd }

private theorem logCoordinates_measurePreserving :
    MeasurePreserving logCoordinates volume volume :=
  (measurePreserving_sub_prod (volume : Measure ℝ) volume).comp (volume_preserving_piFinTwo fun _ => ℝ)

private def gammaConstant (d e : ComplexCharacterData) : ℂ :=
  diagonalConstant d * diagonalConstant e * ((2 : ℂ) ^ (-((min (absWeight d) (absWeight e) : ℕ) : ℂ)) / 16)

private theorem gammaConstant_ne_zero (d e : ComplexCharacterData) : gammaConstant d e ≠ 0 :=
  mul_ne_zero (mul_ne_zero (diagonalConstant_ne_zero d) (diagonalConstant_ne_zero e))
    (div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (by norm_num))

private theorem integral_radialKernel (d e : ComplexCharacterData) (s : ℂ)
    (hsSum : 0 < (zSum d e s).re) (hsGap : 0 < (zGap d e s).re) :
    ∫ y, radialKernel d e s y / 2 ∂logDiagonalMeasure 2 =
      gammaConstant d e * (Gammaℂ (zSum d e s) * Gammaℂ (zGap d e s)) := by
  have hMod : Measurable (rootModulus (n := 2)) :=
    measurable_coe_nnreal_ennreal_iff.mp RealIwasawaQuotientHaar.measurable_rootModulus
  rw [logDiagonalMeasure, integral_withDensity_eq_integral_smul hMod]
  have h (y : Row) : rootModulus y • (radialKernel d e s y / 2) =
      (diagonalConstant d * diagonalConstant e / 2) *
        (logMellin (4 * Real.pi) (zSum d e s) (logCoordinates y).1 *
          logMellin Real.pi (zGap d e s) (2 * (logCoordinates y).2)) := by
    rw [NNReal.smul_def, Complex.real_smul, rootModulus_two, ofReal_exp, radialKernel]
    have hExp : exp ((y 1 - y 0 : ℝ) : ℂ) * exp (((y 0 - y 1 : ℝ) : ℂ) * (zSum d e s + 1)) =
        exp (((y 0 - y 1 : ℝ) : ℂ) * zSum d e s) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    change exp ((y 1 - y 0 : ℝ) : ℂ) *
        (diagonalConstant d * diagonalConstant e *
        ((exp (((y 0 - y 1 : ℝ) : ℂ) * (zSum d e s + 1)) * exp (-((4 * Real.pi * Real.exp (y 0 - y 1) : ℝ) : ℂ))) *
          logMellin Real.pi (zGap d e s) (2 * y 1)) / 2) =
      (diagonalConstant d * diagonalConstant e / 2) *
      ((exp (((y 0 - y 1 : ℝ) : ℂ) * zSum d e s) * exp (-((4 * Real.pi * Real.exp (y 0 - y 1) : ℝ) : ℂ))) *
        logMellin Real.pi (zGap d e s) (2 * y 1))
    rw [← hExp]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  let f := logMellin (4 * Real.pi) (zSum d e s)
  let g := fun x : ℝ => logMellin Real.pi (zGap d e s) (2 * x)
  have hChange := logCoordinates_measurePreserving.integral_comp' (fun p => f p.1 * g p.2)
  change (diagonalConstant d * diagonalConstant e / 2) *
    (∫ y, f (logCoordinates y).1 * g (logCoordinates y).2) = _
  rw [hChange]
  change _ * (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_mul f g]
  dsimp only [f, g]
  rw [integral_logMellin_fourPi _ hsSum, integral_logMellin_pi_twice _ hsGap]
  calc
    _ = (diagonalConstant d * diagonalConstant e *
        (((2 : ℂ) ^ (zGap d e s) * (2 : ℂ) ^ (-zSum d e s)) / 16)) *
        (Gammaℂ (zSum d e s) * Gammaℂ (zGap d e s)) := by ring
    _ = _ := by rw [← cpow_add _ _ two_ne_zero, ← sub_eq_add_neg, zGap_sub_zSum, gammaConstant]

private theorem discreteEqualIntegral_eq (D : RealQuotientMeasureData 1) {d e : ComplexCharacterData}
    (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hW : discreteCoefficient d ∈ realUniformWhittakerModel 1 [.induced d] 1)
    (hV : discreteOppositeCoefficient e ∈ realUniformWhittakerModel 1 [.induced e] (-1))
    {C : ℝ≥0} (hC : 0 < C)
    (hD : D.measure = C • ((logDiagonalMeasure 2).prod compactHaar).map quotientChart)
    (s : ℂ) (hsSum : 0 < (zSum d e s).re) (hsGap : 0 < (zGap d e s).re)
    (hInt : Integrable (realEqualIntegrand (discreteCoefficient d) (discreteOppositeCoefficient e) (rowTest d e) s)
      D.measure) :
    realEqualIntegral D (discreteCoefficient d) (discreteOppositeCoefficient e) (rowTest d e) s =
      ((C : ℂ) * gammaConstant d e) * ((realPairLFactor [.induced d] [.induced e]).denominator s)⁻¹ := by
  let W := discreteCoefficient d
  let V := discreteOppositeCoefficient e
  let Φ := rowTest d e
  let F := realEqualIntegrand W V Φ s
  let H (g : G) := kernel W V Φ g * exp (s * (logDet g : ℂ))
  have hWr := RealLocalWhittaker.model_le_regularFunctions [.induced d] 1
    (RealUniformWhittaker.model_le_model [.induced d] 1 hW)
  have hVr := RealLocalWhittaker.model_le_regularFunctions [.induced e] (-1)
    (RealUniformWhittaker.model_le_model [.induced e] (-1) hV)
  have hHc : Continuous H :=
    (RealEqualConvergence.continuous_kernel hWr.2.1.continuous hVr.2.1.continuous Φ.continuous).mul
      ((continuous_const.mul (continuous_ofReal.comp RealEqualConvergence.continuous_logDet)).cexp)
  have hWV (u : G) (hu : u ∈ Langlands.GeneralLinear.upperUnipotent 2 ℝ) (g : G) :
      W (u * g) * V (u * g) = W g * V g := by
    change discreteCoefficient d (u * g) * discreteOppositeCoefficient e (u * g) = _
    rw [hWr.1 u hu g, hVr.1 u hu g]
    calc
      _ = (realWhittakerCharacter (1 : ℝˣ) u *
          realWhittakerCharacter (-1 : ℝˣ) u) * (W g * V g) := by dsimp [W, V]; ring
      _ = _ := by rw [RealEqualConvergence.realWhittakerCharacter_mul_neg, one_mul]
  have hH (u : Langlands.GeneralLinear.upperUnipotent 2 ℝ) (g : G) : H (u.val * g) = H g := by
    dsimp only [H]
    rw [RealEqualConvergence.kernel_unipotent_mul hWV, RealEqualConvergence.logDet_unipotent_mul]
  have hF : F = Langlands.QuotientIntegration.descend (Langlands.GeneralLinear.upperUnipotent 2 ℝ) H hH :=
    funext (RealEqualConvergence.out_eq_descend H hH)
  have hEval (p : Row × K₂) : F (quotientChart p) = toralKernel d e s p.1 p.2 := by
    rw [hF]
    exact Langlands.QuotientIntegration.descend_mk _ _ _ (torus p.1 * p.2.val)
  let P := (logDiagonalMeasure 2).prod compactHaar
  let q := quotientChart (r := 1)
  have hq : Measurable q := measurable_quotientChart
  have hDP : D.measure = C • P.map q := hD
  have hFInt : Integrable F (P.map q) := by
    change Integrable F D.measure at hInt
    rw [hDP] at hInt
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hC.ne') ENNReal.coe_ne_top).mp hInt
  have hAEM : AEMeasurable q P := hq.aemeasurable
  have hFComp : Integrable (F ∘ q) P := hFInt.comp_aemeasurable hAEM
  have hChartInt : Integrable (fun p : Row × K₂ => toralKernel d e s p.1 p.2) P := by
    exact hFComp.congr (ae_of_all _ hEval)
  let : compactHaar.IsHaarMeasure := compactHaar_isHaar
  let : IsFiniteMeasure compactHaar := by unfold compactHaar; infer_instance
  change (∫ q, F q ∂D.measure) = _
  have hMap := integral_map (f := F) hAEM hFInt.aestronglyMeasurable
  rw [hDP, integral_smul_nnreal_measure, hMap,
    NNReal.smul_def, Complex.real_smul]
  rw [show (fun p => F (q p)) = fun p => toralKernel d e s p.1 p.2 from funext hEval]
  rw [integral_prod _ hChartInt]
  have hAvg (y : Row) : ∫ k, toralKernel d e s y k ∂compactHaar = radialKernel d e s y / 2 :=
    integral_toralKernel hd he hW hV s y (hHc.comp (continuous_const.mul continuous_subtype_val))
  simp_rw [hAvg]
  rw [integral_radialKernel d e s hsSum hsGap, pairFactor_eq]
  ring

private theorem scale_one (d e : ComplexCharacterData) (hd : d.weight ≠ 0) (he : e.weight ≠ 0)
    (hId : IsIrreducibleGKModule (realStandardRep 2 [.induced d]) (realStandardLie 2 [.induced d]))
    (hIe : IsIrreducibleGKModule (realStandardRep 2 [.induced e]) (realStandardLie 2 [.induced e]))
    (D : RealQuotientMeasureData 1) :
    HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest 1 [.induced d] [.induced e] 1 D)
      (realPairLFactor [.induced d] [.induced e]) := by
  let W := discreteCoefficient d
  let V := discreteOppositeCoefficient e
  have hW := discreteCoefficient_mem d hd
  have hV := (realDiscreteRankTwoAngular e he).1
  have hWu : W ∈ realUniformWhittakerModel 1 [.induced d] 1 :=
    RealWhittakerElliptic.realIrreducibleWhittakerModelUniformity 1 [.induced d] 1 hId ▸ hW
  have hVu : V ∈ realUniformWhittakerModel 1 [.induced e] (-1) :=
    RealWhittakerElliptic.realIrreducibleWhittakerModelUniformity 1 [.induced e] (-1) hIe ▸ hV
  obtain ⟨C, hC, hD⟩ := realIwasawaQuotientHaar 1 D compactHaar compactHaar_isHaar
  obtain ⟨σ, hI, _⟩ := RealEqualConvergence.exists_convergence_of_regular D (rowTest d e)
    (RealUniformWhittaker.iteratedRightDerivative_mem_regularFunctions hWu)
    (RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model hWu)
    (RealUniformWhittaker.iteratedRightDerivative_mem_regularFunctions hVu)
    (RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model hVu)
  let c : ℂ := (C : ℂ) * gammaConstant d e
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hC.ne') (gammaConstant_ne_zero d e)
  let W' : realWhittakerModel 1 [.induced d] 1 := ⟨c⁻¹ • W, Submodule.smul_mem _ _ hW⟩
  let V' : realWhittakerModel 1 [.induced e] (-1) := ⟨V, hV⟩
  let L := realPairLFactor [.induced d] [.induced e]
  refine ⟨1, fun _ => (W', V', rowTest d e), fun _ => ⟨fun _ => 1, fun _ _ => analyticAt_const, ?_⟩,
    fun s => by simp⟩
  refine ⟨max σ (max (-(zSum d e 0).re) (-(zGap d e 0).re)), fun s hs => ?_⟩
  have hsI : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsSum : 0 < (zSum d e s).re := by
    have hle : -(zSum d e 0).re ≤ max σ (max (-(zSum d e 0).re) (-(zGap d e 0).re)) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hh := lt_of_le_of_lt hle hs
    simp only [zSum, add_re, zero_add] at hh ⊢
    linarith
  have hsGap : 0 < (zGap d e s).re := by
    have hle : -(zGap d e 0).re ≤ max σ (max (-(zSum d e 0).re) (-(zGap d e 0).re)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hh := lt_of_le_of_lt hle hs
    simp only [zGap, add_re, zero_add] at hh ⊢
    linarith
  change realEqualIntegral D (c⁻¹ • W) V (rowTest d e) s = 1 * (L.denominator s)⁻¹
  have hScale : realEqualIntegral D (c⁻¹ • W) V (rowTest d e) s =
      c⁻¹ * realEqualIntegral D W V (rowTest d e) s := by
    simp only [realEqualIntegral, ArchimedeanLocal.equalIntegral, ArchimedeanLocal.equalIntegrand,
      Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hScale, discreteEqualIntegral_eq D hd he hWu hVu hC hD s hsSum hsGap (hI s hsI),
    ← mul_assoc, inv_mul_cancel₀ hc]

/-- Two irreducible nonzero-weight real discrete blocks admit covering ordinary normalized tests
at every additive scale, with a finite sum equal to one at the two scales of absolute value one. -/
def RealEqualDiscreteGenerationStatement : Prop :=
  ∀ (d e : ComplexCharacterData), d.weight ≠ 0 → e.weight ≠ 0 →
    IsIrreducibleGKModule (realStandardRep 2 [.induced d]) (realStandardLie 2 [.induced d]) →
    IsIrreducibleGKModule (realStandardRep 2 [.induced e]) (realStandardLie 2 [.induced e]) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData 1),
      HasCoveringOrdinaryNormalizations
        (realOrdinaryEqualTest 1 [.induced d] [.induced e] a D) (realPairLFactor [.induced d] [.induced e]) ∧
      ((a = 1 ∨ a = -1) → HasFiniteOrdinaryNormalizationSum
        (realOrdinaryEqualTest 1 [.induced d] [.induced e] a D) (realPairLFactor [.induced d] [.induced e]))

theorem realEqualDiscreteGeneration : RealEqualDiscreteGenerationStatement := by
  intro d e hd he hId hIe a D
  have h := scale_one d e hd he hId hIe (RealCharacterChange.leadingCharacterMeasure 1 a D)
  refine ⟨RealCharacterChange.realEqualCoverage_scale a D h.covering, fun ha => ?_⟩
  exact RealCharacterChange.realEqualFiniteSum_scale a (by rcases ha with rfl | rfl <;> simp) D h

end Langlands.Global.RankinSelbergGlobal.RealEqualDiscreteGeneration
