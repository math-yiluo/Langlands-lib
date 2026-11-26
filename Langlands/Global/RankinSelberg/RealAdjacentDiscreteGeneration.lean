import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealDiscreteRankTwoWhittaker
import Langlands.Global.RankinSelberg.RealGodementSpectralContinuation
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Representation.Archimedean.RealRankOneStandardModule

/-! # A normalized real `GL₂ × GL₁` test for the discrete block -/

noncomputable section

open Complex MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.RankinSelbergGlobal.RealAdjacentDiscreteGeneration

open ArchimedeanLocal RealDiscreteRankTwoWhittaker RealRankZero
open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.GramFormula (realPositionExponent)
open RealRankOneStandardModule (characterVector characterVector_mem)
open Langlands.GodementJacquet (tateScalarEquiv)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

private local instance : MeasurableSpace ℝˣ := borel _
private local instance : BorelSpace ℝˣ := ⟨rfl⟩

private def gammaArgument (d : ComplexCharacterData) (e : RealCharacterData) (s : ℂ) : ℂ :=
  s + d.exponent + e.exponent + (d.weight.natAbs : ℂ) / 2

private theorem pairFactor_eq (d : ComplexCharacterData) (e : RealCharacterData) (s : ℂ) :
    ((realPairLFactor [.induced d] [.character e]).denominator s)⁻¹ = Gammaℂ (gammaArgument d e s) := by
  change ((realLFactor [.induced (d.twistReal e)]).denominator s)⁻¹ = _
  rw [realLFactor_singleton, RealBlock.lFactor_induced, ReciprocalEntire.denominator_shift]
  change ((Gammaℂ (s + ((d.exponent + e.exponent) + (d.weight.natAbs : ℂ) / 2)))⁻¹)⁻¹ = _
  rw [inv_inv, gammaArgument]
  congr 1
  ring

private def positiveKernel (d : ComplexCharacterData) (e : RealCharacterData) (s : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then diagonalConstant d * ((x : ℂ) ^ gammaArgument d e s *
    exp (-(((2 * Real.pi) * x : ℝ) : ℂ))) else 0

private theorem unequalIntegrand_eq_positiveKernel (d : ComplexCharacterData) (hd : d.weight ≠ 0)
    (e : RealCharacterData) (s : ℂ) (u : ℝˣ) :
    realUnequalIntegrand (Nat.lt_succ_self 0) (discreteCoefficient d) (characterVector e) s
      (quotientUnits.symm u) = positiveKernel d e s u := by
  change discreteCoefficient d (padGL _ (quotientUnits.symm u).out) *
    characterVector e (quotientUnits.symm u).out *
      ArchimedeanLocal.detPower realNormalizedAbs (quotientUnits.symm u).out (s - ((1 - 0 : ℕ) : ℂ) / 2) = _
  rw [quotientUnits_symm_out, show padGL (by decide : 0 + 1 ≤ 1 + 1) (tateScalarEquiv ℝ u) =
    diagonalPoint u from rfl, (realDiscreteRankTwoWhittaker d hd).2 u]
  by_cases hu : 0 < (u : ℝ)
  · rw [positiveKernel, ite_eq_left hu, ite_eq_left hu, detPower_tateScalarEquiv, abs_of_pos hu]
    have hV : characterVector e (tateScalarEquiv ℝ u) = ((u : ℝ) : ℂ) ^ e.exponent := by
      change (e.character (GeneralLinear.determinant (tateScalarEquiv ℝ u)) : ℂ) = _
      rw [determinant_tateScalarEquiv, e.character_eq, abs_of_pos hu, div_self hu.ne']
      simp
    rw [hV]
    simp only [Nat.sub_zero, Nat.cast_one]
    let b : ℂ := (u : ℝ)
    have hb : b ≠ 0 := ofReal_ne_zero.mpr u.ne_zero
    have hpow : b ^ diagonalExponent d * b ^ e.exponent * b ^ (s - 1 / 2) =
        b ^ gammaArgument d e s := by
      rw [← cpow_add _ _ hb, ← cpow_add _ _ hb]
      congr 1
      simp only [diagonalExponent, gammaArgument, Nat.cast_add, Nat.cast_one]
      ring
    linear_combination (diagonalConstant d * exp (-(((2 * Real.pi) * (u : ℝ) : ℝ) : ℂ))) * hpow
  · simp [positiveKernel, hu]

private theorem positiveKernel_mellin (d : ComplexCharacterData) (e : RealCharacterData) (s : ℂ)
    (hs : 0 < (gammaArgument d e s).re) :
    (∫ u : ℝˣ, positiveKernel d e s u ∂unitsHaar) =
      (diagonalConstant d / 2) * Gammaℂ (gammaArgument d e s) := by
  rw [integral_unitsHaar]
  let z := gammaArgument d e s
  let r : ℝ := 2 * Real.pi
  have hr : 0 < r := by dsimp [r]; positivity
  have hG (x : ℝ) : ((|x|⁻¹ : ℝ) : ℂ) * positiveKernel d e s x =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => diagonalConstant d * ((t : ℂ) ^ (z - 1) *
        exp (-((r * t : ℝ) : ℂ)))) x := by
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), positiveKernel, ite_eq_left hx,
        abs_of_pos hx, ofReal_inv]
      have hP : (x : ℂ)⁻¹ * (x : ℂ) ^ z = (x : ℂ) ^ (z - 1) := by
        rw [← cpow_neg_one, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
        congr 1
        ring
      linear_combination (diagonalConstant d * exp (-((r * x : ℝ) : ℂ))) * hP
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), positiveKernel, ite_eq_right hx, mul_zero]
  simp_rw [hG]
  simp_rw [Complex.ofReal_mul]
  have hR : (r : ℂ) = 2 * (Real.pi : ℂ) := by simp [r]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs hr,
    Gammaℂ_def, one_div, inv_cpow_ofReal_nonneg hr.le, ← cpow_neg, hR]
  ring

private theorem discreteUnequalIntegral_eq (D : RealQuotientMeasureData 0) (d : ComplexCharacterData)
    (hd : d.weight ≠ 0) (e : RealCharacterData) {κ : ℝ≥0}
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm) (s : ℂ) (hs : 0 < (gammaArgument d e s).re) :
    realUnequalIntegral (Nat.lt_succ_self 0) D (discreteCoefficient d) (characterVector e) s =
      ((κ : ℂ) * (diagonalConstant d / 2)) * ((realPairLFactor [.induced d] [.character e]).denominator s)⁻¹ := by
  let F := realUnequalIntegrand (Nat.lt_succ_self 0) (discreteCoefficient d) (characterVector e) s
  change (∫ q, F q ∂D.measure) = _
  rw [hκ, integral_smul_nnreal_measure, quotientUnits.symm.measurableEmbedding.integral_map F,
    NNReal.smul_def, Complex.real_smul]
  simp_rw [show ∀ u, F (quotientUnits.symm u) = positiveKernel d e s u from
    unequalIntegrand_eq_positiveKernel d hd e s]
  rw [positiveKernel_mellin d e s hs, pairFactor_eq]
  ring

/-- With an induced real block of nonzero weight and a real character, a single
ordinary scale-one test has normalized value one on the whole spectral plane. -/
def RealAdjacentDiscreteGenerationStatement : Prop :=
  ∀ (d : ComplexCharacterData), d.weight ≠ 0 → ∀ (e : RealCharacterData) (D : RealQuotientMeasureData 0),
    HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest (Nat.lt_succ_self 0) [.induced d] [.character e] 1 D)
      (realPairLFactor [.induced d] [.character e])

theorem realAdjacentDiscreteGeneration : RealAdjacentDiscreteGenerationStatement := by
  intro d hd e D
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq D
  let C : ℂ := (κ : ℂ) * (diagonalConstant d / 2)
  have hC : C ≠ 0 := mul_ne_zero (by exact_mod_cast hκ0) (div_ne_zero (diagonalConstant_ne_zero d) two_ne_zero)
  have hW := discreteCoefficient_mem d hd
  have hV : characterVector e ∈ realWhittakerModel 0 [.character e] (-1) := by
    apply RealUniformWhittaker.model_le_model
    let f : Automorphic.realStandardKFinite 1 [.character e] := ⟨characterVector e, characterVector_mem e⟩
    have hd0 : PartialJacquet.IsStrictlyDominant (realPositionExponent [.character e]) 0 :=
      fun _ h => (Nat.not_lt_zero _ h).elim
    have h := RealGodement.realGodementOpenCellModel 0 [.character e] 1 hd0 f
    change RealGodement.additiveJacquetIntegral 1 (characterVector e) ∈ _ at h
    simpa only [funext (RealGodement.additiveJacquetIntegral_rankOne 1 (characterVector e))] using h
  let W : realWhittakerModel 1 [.induced d] 1 := ⟨C⁻¹ • discreteCoefficient d, Submodule.smul_mem _ _ hW⟩
  let V : realWhittakerModel 0 [.character e] (-1) := ⟨characterVector e, hV⟩
  let L := realPairLFactor [.induced d] [.character e]
  refine ⟨1, fun _ => (W, V), fun _ => ⟨fun _ => 1, fun _ _ => analyticAt_const, ?_⟩, fun s => by simp⟩
  refine ⟨-(gammaArgument d e 0).re, fun s hs => ?_⟩
  have hs' : 0 < (gammaArgument d e s).re := by
    simp only [gammaArgument, add_re, zero_add] at hs ⊢
    linarith
  change realUnequalIntegral _ D (C⁻¹ • discreteCoefficient d) (characterVector e) s =
    1 * (L.denominator s)⁻¹
  have hScale : realUnequalIntegral (Nat.lt_succ_self 0) D (C⁻¹ • discreteCoefficient d) (characterVector e) s =
      C⁻¹ * realUnequalIntegral (Nat.lt_succ_self 0) D (discreteCoefficient d) (characterVector e) s := by
    simp only [realUnequalIntegral, ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.unequalIntegrand,
      Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hScale, discreteUnequalIntegral_eq D d hd e hκ s hs', ← mul_assoc, inv_mul_cancel₀ hC]

end Langlands.Global.RankinSelbergGlobal.RealAdjacentDiscreteGeneration
