import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.Analysis.Local.HaarInversionDensityProof
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.Analysis.Distribution.TemperateGrowth

/-! # Real general-linear Haar measure and integrable height decay -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.RankinSelberg.GLDeterminantDensity
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Frobenius NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealPlaceRestriction

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

private def scalarLebesgueHaar : AdditiveHaarMeasure ℝ where
  measure := volume
  isAddHaar := inferInstance
  regular := inferInstance

/-- Lebesgue measure in every real square matrix entry. -/
def realMatrixVolume (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  rectangularMeasure scalarLebesgueHaar n n

local instance (n : ℕ) : (realMatrixVolume n).IsAddHaarMeasure := by
  unfold realMatrixVolume
  infer_instance

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ

private theorem realVolume_map_mul (a : ℝ) (ha : a ≠ 0) :
    (volume : Measure ℝ).map (fun x => a * x) = (‖a‖₊)⁻¹ • (volume : Measure ℝ) := by
  change (volume : Measure ℝ).map (fun x => a • x) = _
  rw [Measure.map_addHaar_smul volume ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private theorem realMatrixVolume_map_left (g : G) :
    (realMatrixVolume n).map (fun A => g.val * A) = weight n nnnormHom g • (realMatrixVolume n) := by
  have h := haarMeasure_map_rectangular (volume : Measure ℝ) (nnnormHom : ℝ →*₀ ℝ≥0)
    realVolume_map_mul (realMatrixVolume n) g.val (1 : M) (determinant g).ne_zero (by simp)
  simpa only [Matrix.mul_one, Matrix.det_one, map_one, one_pow, mul_one, Fintype.card_fin,
    weight_eq, matrixWeight, inv_pow] using h

/-- The usual matrix Haar measure `|det A|⁻ⁿ dA` on the invertible locus. -/
def realMatrixHaar (n : ℕ) : Measure (Langlands.GeneralLinear n ℝ) :=
  weightedRestriction n nnnormHom (realMatrixVolume n)

theorem realMatrixHaar_isHaar (n : ℕ) : (realMatrixHaar n).IsHaarMeasure := by
  unfold realMatrixHaar
  exact weightedRestriction_isHaar (K := ℝ) n nnnormHom continuous_nnnorm
    (realMatrixVolume n) (fun g => realMatrixVolume_map_left g)

/-- The determinant-density measure is a fixed positive multiple of any supplied Haar measure. -/
theorem exists_realMatrixHaar_eq_smul (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ realMatrixHaar n = c • μ := by
  unfold realMatrixHaar
  exact exists_weightedRestriction_eq_smul (K := ℝ) n nnnormHom continuous_nnnorm
    (realMatrixVolume n) (fun g => realMatrixVolume_map_left g) μ

/-- Every real general-linear Haar measure is right invariant and inversion invariant. -/
theorem realMatrixHaar_symmetries (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  let _ : PseudoMetrizableSpace G := Units.isOpenEmbedding_val.isInducing.pseudoMetrizableSpace
  let _ : μ.Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hscalar (a : ℝˣ) :
      modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin n) a) = 1 := by
    change modularCharacterFun _ = 1
    rw [modularCharacterFun_eq_haarScalarFactor μ]
    have he : (fun x : G => x * Matrix.GeneralLinearGroup.scalar (Fin n) a) =
        fun x => Matrix.GeneralLinearGroup.scalar (Fin n) a * x :=
      funext fun x => (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    have hmap : μ.map (fun x : G => x * Matrix.GeneralLinearGroup.scalar (Fin n) a) = μ := by
      rw [he, map_mul_left_eq_self]
    have hSelf (ν : Measure G) [ν.IsHaarMeasure] (hν : ν = μ) : haarScalarFactor ν μ = 1 := by
      subst ν
      exact haarScalarFactor_self μ
    exact hSelf _ hmap
  have hMod : ∀ g : G, modularCharacter g = 1 :=
    GeneralLinearUnimodularity.character_eq_one modularCharacter hscalar
  refine ⟨⟨fun g => ?_⟩, ⟨?_⟩⟩
  · rw [map_right_mul_eq_modularCharacterFun_smul μ g,
      show modularCharacterFun g = 1 from hMod g, one_smul]
  · have h := (Langlands.Haar.haarInversionDensity G μ).1
    have hw : (fun g : G => (modularCharacter g : ℝ≥0∞)) = 1 := by
      funext g
      rw [hMod, ENNReal.coe_one]
      rfl
    rw [hw, withDensity_one] at h
    exact h

/-- Some negative power of the actual real matrix height is integrable against
any Haar measure on a positive-rank real general linear group. -/
theorem exists_integrable_realMatrixHeight_inv_pow (hn : 0 < n) (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ p : ℕ, Integrable (fun g : G => (realMatrixHeight g ^ p)⁻¹) μ := by
  obtain ⟨c, hc, hμ⟩ := exists_realMatrixHaar_eq_smul μ
  let l := (realMatrixVolume n).integrablePower
  let b : M → ℝ := fun A => ((1 + ‖A‖) ^ l)⁻¹
  have hb : Integrable b (realMatrixVolume n) := ((realMatrixVolume n).integrable_pow_neg_integrablePower).congr
    (Filter.Eventually.of_forall fun A => by
      simp only [b, l, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖A‖), Real.rpow_natCast])
  have hMaj : Integrable (fun g : G => |g.val.det| ^ n * b g.val) μ := by
    unfold realMatrixHaar at hμ
    have h := (integrable_forwardWeight_iff_of_eq_smul (K := ℝ) (E := ℝ) n nnnormHom continuous_nnnorm
      (realMatrixVolume n) μ c hc hμ b).2 hb.integrableOn
    simpa only [forwardWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, nnnormHom_apply,
      coe_nnnorm, Real.norm_eq_abs] using h
  obtain ⟨C, d, _, hD⟩ := exists_det_rpow_le_realMatrixHeight hn (-(n : ℝ))
  refine ⟨d + l, (hMaj.const_mul (C * 2 ^ l)).mono' ?_ ?_⟩
  · have hH : Continuous (fun g : G => realMatrixHeight g) := by
      simp_rw [realMatrixHeight_eq_frobenius]
      exact (Units.continuous_val.norm.pow 2).add (Units.continuous_coe_inv.norm.pow 2)
    exact ((hH.pow _).inv₀ (fun g =>
      pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) (two_le_realMatrixHeight hn g))))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    let H := realMatrixHeight g
    have hHtwo : 2 ≤ H := two_le_realMatrixHeight hn g
    have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHtwo
    have hDet : 0 < |g.val.det| := abs_pos.mpr (determinant g).ne_zero
    have hBound : (|g.val.det| ^ n)⁻¹ ≤ C * H ^ d := by
      simpa only [Real.rpow_neg hDet.le, Real.rpow_natCast] using hD g
    have hInv : (H ^ d)⁻¹ ≤ C * |g.val.det| ^ n := by
      rw [← one_div]
      apply (div_le_iff₀ (pow_pos hH _)).mpr
      have h := mul_le_mul_of_nonneg_right hBound (pow_pos hDet n).le
      rw [inv_mul_cancel₀ (pow_ne_zero n hDet.ne')] at h
      simpa only [mul_assoc, mul_comm (H ^ d)] using h
    have hA : ‖g.val‖ ≤ H := by
      have hS : ‖g.val‖ ^ 2 ≤ H := by
        dsimp only [H]
        rw [realMatrixHeight_eq_frobenius]
        exact le_add_of_nonneg_right (sq_nonneg _)
      nlinarith [sq_nonneg (‖g.val‖ - 1)]
    have hPow : (1 + ‖g.val‖) ^ l ≤ 2 ^ l * H ^ l := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hV : (H ^ l)⁻¹ ≤ 2 ^ l * b g.val := by
      have h : (1 : ℝ) / H ^ l ≤ (2 : ℝ) ^ l / (1 + ‖g.val‖) ^ l :=
        (div_le_div_iff₀ (pow_pos hH _) (by positivity)).mpr (by simpa only [one_mul] using hPow)
      simpa only [b, div_eq_mul_inv, one_mul] using h
    change ‖(H ^ (d + l))⁻¹‖ ≤ (C * 2 ^ l) * (|g.val.det| ^ n * b g.val)
    rw [Real.norm_of_nonneg (by positivity), pow_add, mul_inv]
    calc
      _ ≤ (C * |g.val.det| ^ n) * (2 ^ l * b g.val) :=
        mul_le_mul hInv hV (by positivity) (le_trans (by positivity) hInv)
      _ = _ := by ring

/-- Exact determinant-density normalization, Haar symmetries, and integrable
matrix-height decay on positive-rank real general linear groups. -/
def RealGodementHaarStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure],
    (∃ c : ℝ≥0, 0 < c ∧ realMatrixHaar n = c • μ) ∧
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant ∧
    ∃ p : ℕ, Integrable (fun g => (realMatrixHeight g ^ p)⁻¹) μ

theorem realGodementHaar : RealGodementHaarStatement := by
  intro n hn μ _
  exact ⟨exists_realMatrixHaar_eq_smul μ, (realMatrixHaar_symmetries μ).1,
    (realMatrixHaar_symmetries μ).2, exists_integrable_realMatrixHeight_inv_pow hn μ⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
