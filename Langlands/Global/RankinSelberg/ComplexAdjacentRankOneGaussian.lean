import Langlands.Global.RankinSelberg.ComplexAdjacentRankOneStripGrowth
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitIntegrals
import Langlands.Global.RankinSelberg.ComplexRankZeroNormalization

/-! # The product of the two Tate tests in the complex adjacent rank-one unfolding -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.GodementJacquet (tateScalarEquiv)
open ArchimedeanLocal
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementColumnProduct (columnProduct)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexRankZero (characterFunction unitsHaar)
open Langlands.LocalFactor.ComplexTate (gaussSchwartz gaussSchwartz_apply zeta_gaussian gaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

attribute [local instance] ComplexRankZero.unitsMeasurable ComplexRankZero.unitsBorel

local notation "G" => Langlands.GeneralLinear 1 ℂ
local notation "G₂" => Langlands.GeneralLinear 2 ℂ
local notation "Mat" => Matrix (Fin 1) (Fin 1) ℂ
local notation "Vec" => Fin 1 → ℂ
local notation "gap" => Nat.lt_succ_self 0

private local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

private def squareEntry : Mat ≃L[ℝ] ℂ :=
  ({ toFun X := X 0 0
     invFun z := Matrix.of fun _ _ => z
     left_inv X := by
       ext i j
       rw [show i = 0 from Subsingleton.elim _ _, show j = 0 from Subsingleton.elim _ _]
       rfl
     right_inv z := rfl
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat ≃ₗ[ℝ] ℂ).toContinuousLinearEquiv

/-- The angular Tate Gaussian on a square matrix of size one. -/
def rankOneSquareGaussian (m : ℤ) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ squareEntry (gaussSchwartz m)

@[simp] theorem rankOneSquareGaussian_apply (m : ℤ) (X : Mat) :
    rankOneSquareGaussian m X = gaussian m (X 0 0) := gaussSchwartz_apply m (X 0 0)

/-- The angular Tate Gaussian on a row of size one. -/
def rankOneRowGaussian (m : ℤ) : 𝓢(Vec, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℂ) (gaussSchwartz m)

@[simp] theorem rankOneRowGaussian_apply (m : ℤ) (v : Vec) :
    rankOneRowGaussian m v = gaussian m (v 0) := gaussSchwartz_apply m (v 0)

/-- The positive standard trace transform exchanges the two angular weights. -/
theorem splitRowTransform_one_rankOneRowGaussian (m : ℤ) (z : ℂ) :
    splitRowTransform (1 : ℂˣ) (rankOneRowGaussian m) (fun _ => z) =
      Complex.I ^ m.natAbs * gaussian (-m) z := by
  have hF : splitRowTransform (1 : ℂˣ) (rankOneRowGaussian m) (fun _ => z) =
      complexFourierTransform (1 : ℂˣ) (rankOneRowGaussian m) (fun _ => z) := by
    rw [splitRowTransform_apply]
    unfold splitRowPlus complexFourierTransform ArchimedeanLocal.fourierTransform
      Langlands.HarmonicAnalysis.rowMeasure
    simp_rw [mul_comm z]
  rw [hF]
  rw [ComplexRankZero.complexFourierTransform_const]
  have h := Langlands.LocalFactor.ComplexTate.integral_exp_mul_gaussian m z
  simpa [ComplexRankZero.ComplexTate.tateFourier, Langlands.LocalFactor.ComplexTate.measure,
    ComplexRankZero.lineSchwartz_apply] using h

private theorem integral_rankOneSquareGaussian (μ : Measure G) [μ.IsHaarMeasure]
    (d e : ComplexCharacterData) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ s : ℂ, 0 < (s + (d.mul e).exponent).re →
      (∫ g, ComplexSquareZeta.zetaKernel (rankOneSquareGaussian (d.mul e).weight)
        (characterFunction (d.mul e)) s g ∂μ) =
      k * ((complexPairLFactor [d] [e]).denominator s)⁻¹ := by
  let emb := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) 1
  let : LocallyCompactSpace G := emb.locallyCompactSpace
  let : SecondCountableTopology G := emb.secondCountableTopology
  let E := tateScalarEquiv ℂ
  let : (μ.map E.symm).IsHaarMeasure := E.symm.isHaarMeasure_map μ
  let k := Measure.haarScalarFactor (μ.map E.symm) unitsHaar
  have hk : 0 < k := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hμ : μ.map E.symm = k • unitsHaar := Measure.isMulLeftInvariant_eq_smul _ _
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨(k : ℂ) / 2, div_ne_zero hkC two_ne_zero, fun s hs => ?_⟩
  let b := d.mul e
  let F (z : ℂ) := gaussian b.weight z * (z / (‖z‖ : ℂ)) ^ b.weight * (‖z‖ : ℂ) ^ (2 * s + 2 * b.exponent)
  have heq (u : ℂˣ) : ComplexSquareZeta.zetaKernel (rankOneSquareGaussian b.weight)
      (characterFunction b) s (E u) = F u := by
    rw [ComplexSquareZeta.zetaKernel, rankOneSquareGaussian_apply]
    have hX : (E u).val 0 0 = (u : ℂ) := by
      rw [← ComplexRankZero.det_val_tateScalarEquiv u, Matrix.det_fin_one]
    have hdet : determinant (E u) = u := ComplexRankZero.determinant_tateScalarEquiv u
    rw [hX, characterFunction, hdet, b.character_eq]
    simp only [Nat.cast_one, sub_self, zero_div, add_zero]
    have hu : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr u.ne_zero
    have huC : (‖(u : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    change _ * _ * (Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC (u : ℂ)) ^ s = _
    rw [Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC, pow_two,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le hu.le, ← Complex.cpow_add _ _ huC]
    dsimp only [F]
    rw [mul_assoc, mul_assoc, ← Complex.cpow_add _ _ huC]
    ring_nf
  have hMap := (E.symm.toHomeomorph.measurableEmbedding.integral_map (μ := μ)
    (fun u : ℂˣ => ComplexSquareZeta.zetaKernel (rankOneSquareGaussian b.weight)
      (characterFunction b) s (E u)))
  change (∫ u, ComplexSquareZeta.zetaKernel (rankOneSquareGaussian b.weight)
    (characterFunction b) s (E u) ∂μ.map E.symm) =
    (∫ g, ComplexSquareZeta.zetaKernel (rankOneSquareGaussian b.weight)
      (characterFunction b) s (E (E.symm g)) ∂μ) at hMap
  simp only [ContinuousMulEquiv.apply_symm_apply] at hMap
  rw [hμ] at hMap
  rw [← hMap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp_rw [heq]
  rw [ComplexRankZero.integral_unitsHaar F]
  have hIntegrand : (fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * F z) =ᵐ[volume]
      ComplexRankZero.ComplexTate.integrand (gaussian b.weight) b.weight b.exponent s := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
    rw [ComplexRankZero.ComplexTate.integrand, ite_eq_right hz]
    have hzC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hz).ne'
    simp only [F, Complex.ofReal_inv, Complex.ofReal_pow]
    rw [show 2 * (s + b.exponent) - 2 = (2 * s + 2 * b.exponent) - 2 by ring,
      Complex.cpow_sub _ _ hzC, Complex.cpow_two, div_eq_mul_inv]
    ring
  rw [integral_congr_ae hIntegrand, ComplexRankZero.complexPairLFactor_singleton, inv_inv]
  have hz : ComplexRankZero.ComplexTate.zeta (gaussian b.weight) b.weight b.exponent s =
      Complex.Gammaℂ (s + b.exponent + (b.weight.natAbs : ℂ) / 2) := zeta_gaussian _ hs
  rw [ComplexRankZero.ComplexTate.zeta, ComplexRankZero.ComplexTate.integral_two_smul] at hz
  rw [← add_assoc, ← hz]
  ring

/-- Use angular Tate tests in the split `GL₂ × GL₁` unfolding. The resulting
continued Godement coefficient has ordinary integral a nonzero constant times
its prescribed pair factor on a right half-plane. -/
def ComplexAdjacentRankOneGaussianProductStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData 0) [SFinite D.measure] (a : ℂˣ) (d c e : ComplexCharacterData)
    (U : complexWhittakerModel 0 [c] (-a)) (V : complexWhittakerModel 0 [e] a),
    U.val ≠ 0 → V.val ≠ 0 → ∀ (φ : 𝓢(Vec, ℂ)) (C : ℂ), C ≠ 0 →
    (∀ z : ℂ, splitRowTransform a φ (fun _ => z) = C * gaussian (c.mul e).weight z) →
    let Φ := rankOneSquareGaussian (d.mul e).weight
    let W (g : G₂) := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProduct Φ φ)) U.val g 0
    ∃ (k : ℂ) (σ : ℝ), k ≠ 0 ∧ ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral gap D W V.val s =
        k * ((complexPairLFactor [d, c] [e]).denominator s)⁻¹

theorem complexAdjacentRankOneGaussianProduct : ComplexAdjacentRankOneGaussianProductStatement := by
  intro D hD a d c e U V hU hV φ C hC hφ Φ W
  obtain ⟨Cu, hu⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel U.2
  obtain ⟨Cv, hv⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel V.2
  have hCu : Cu ≠ 0 := fun h => hU (funext fun g => by simp [hu g, h])
  have hCv : Cv ≠ 0 := fun h => hV (funext fun g => by simp [hv g, h])
  obtain ⟨κ, hκ0, hκ⟩ := ComplexRankZero.exists_measure_eq D
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  obtain ⟨k, hk, hZ⟩ := integral_rankOneSquareGaussian D.groupHaar d e
  obtain ⟨σ, hσ⟩ := complexAdjacentSplitIntegrals (r := 0) D a d 0 Φ φ [c] [e] rfl rfl U V
  let A : ℂ := (κ : ℂ) / 2 * (Cu * Cv)
  let S : ℂ := d.character ((-1 : ℂˣ) ^ (0 + 1))
  refine ⟨S * (k * (A * C)), max σ (max (-(d.mul e).exponent.re) (-(c.mul e).exponent.re)),
    mul_ne_zero (Units.ne_zero _) (mul_ne_zero hk (mul_ne_zero
      (mul_ne_zero (div_ne_zero hκC two_ne_zero) (mul_ne_zero hCu hCv)) hC)), fun s hs => ?_⟩
  have hds : 0 < (s + (d.mul e).exponent).re := by
    rw [Complex.add_re]
    linarith [lt_of_le_of_lt (le_max_left (-(d.mul e).exponent.re) (-(c.mul e).exponent.re))
      ((le_max_right σ _).trans_lt hs)]
  have hcs : 0 < (s + (c.mul e).exponent).re := by
    rw [Complex.add_re]
    linarith [lt_of_le_of_lt (le_max_right (-(d.mul e).exponent.re) (-(c.mul e).exponent.re))
      ((le_max_right σ _).trans_lt hs)]
  have hLine : (ComplexRankZero.lineSchwartz (splitRowTransform a φ) : ℂ → ℂ) =
      fun z => C * gaussian (c.mul e).weight z :=
    funext fun z => (ComplexRankZero.lineSchwartz_apply _ z).trans (hφ z)
  have hE : complexEqualIntegral D U.val V.val (splitRowTransform a φ) s =
      (A * C) * ((complexPairLFactor [c] [e]).denominator s)⁻¹ := by
    rw [ComplexRankZero.equalIntegral_eq c e hκ hu hv, hLine, ComplexRankZero.complexPairLFactor_singleton,
      inv_inv, ← add_assoc]
    change A * Langlands.LocalFactor.ComplexTate.zeta (fun z => C * gaussian (c.mul e).weight z)
      (c.mul e).weight (s + (c.mul e).exponent) = _
    rw [Langlands.LocalFactor.ComplexTate.zeta_const_mul, zeta_gaussian _ hcs]
    dsimp only [A]
    ring
  have hP := (hσ s ((le_max_left σ _).trans_lt hs)).2.2.1
  change complexUnequalIntegral gap D W V.val s = S * _ at hP
  simp only [Nat.cast_zero, zero_div, add_zero] at hP
  rw [hP]
  simp_rw [unfoldedKernel_eq_prod_for_character d e Φ (splitRowTransform a φ) U.val V.val Cv hv s]
  rw [integral_prod_mul, hZ s hds]
  change S * ((k * ((complexPairLFactor [d] [e]).denominator s)⁻¹) *
    complexEqualIntegral D U.val V.val (splitRowTransform a φ) s) = _
  rw [hE, pairFactor_two_one, Langlands.LocalFactor.ReciprocalEntire.denominator_mul, mul_inv]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
