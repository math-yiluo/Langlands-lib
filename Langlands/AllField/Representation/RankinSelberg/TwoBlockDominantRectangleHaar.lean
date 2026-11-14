import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-!
# Exact supplied Haar measure on the two dominant rectangles

The determinant-one laws of the actual multipliers imply preservation of the
supplied product measure. Both rectangle dimensions may be zero.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding integrable_rectangleChange_iff integral_rectangleChange measurePreserving_rectangleChange rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uE

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance rectangleHaarSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance rectangleHaarMeasurable : MeasurableSpace F := borel _
local instance rectangleHaarBorel : BorelSpace F := ⟨rfl⟩
local instance rectangleMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
local instance rectangleMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))
local instance rectanglesBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F) :=
  inferInstanceAs (BorelSpace
    (Matrix (Fin (m 0 + 1)) (Fin k) F ×
      Matrix (Fin j) (Fin (m 1 + 1)) F))

/-- The exact nested product of the supplied scalar additive Haar measure. -/
def rectangleMeasure (m : Fin 2 → ℕ) (j k : ℕ)
    (ν : AdditiveHaarMeasure F) : Measure (Rectangles m j k F) :=
  (rectangularMeasure ν (m 0 + 1) k).prod (rectangularMeasure ν j (m 1 + 1))

instance rectangleMeasure_sigmaFinite (m : Fin 2 → ℕ) (j k : ℕ)
    (ν : AdditiveHaarMeasure F) :
    SigmaFinite (rectangleMeasure F m j k ν) := by
  unfold rectangleMeasure
  infer_instance

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The already constructed rectangle equivalence, with its proved topology. -/
def rectangleChangeHomeomorph (j k : ℕ) (u : lowerBlockUnipotent h F) :
    Rectangles m j k F ≃ₜ Rectangles m j k F where
  toEquiv := (rectangleChange h j k u).toEquiv
  continuous_toFun := continuous_rectangleChange h j k u
  continuous_invFun := continuous_rectangleChange_symm h j k u

private theorem determinantNorm_of_det_one {n : ℕ} (A : GeneralLinear n F)
    (hA : Matrix.det A.val = 1) :
    (⟨⟩ : LocalFieldData F).determinantNorm n A = 1 := by
  have hd : GeneralLinear.determinant A = 1 := Units.ext hA
  change (⟨⟩ : LocalFieldData F).normalizedAbsUnits
    (GeneralLinear.determinant A) = 1
  rw [hd, map_one]

/-- The actual simultaneous change preserves the exact product for every supplied
additive Haar, including either empty rectangle. No Jacobian premise is required. -/
theorem measurePreserving_rectangleChange (j k : ℕ)
    (ν : AdditiveHaarMeasure F) (u : lowerBlockUnipotent h F) :
    MeasurePreserving (rectangleChange h j k u)
      (rectangleMeasure F m j k ν) (rectangleMeasure F m j k ν) := by
  have hA := determinantNorm_of_det_one F (leftMultiplier h u) (det_leftMultiplier h u)
  have hB := determinantNorm_of_det_one F (rightMultiplier h u) (det_rightMultiplier h u)
  have hx : MeasurePreserving
      (fun x : Matrix (Fin (m 0 + 1)) (Fin k) F =>
        ((leftMultiplier h u)⁻¹).val * x)
      (rectangularMeasure ν (m 0 + 1) k) (rectangularMeasure ν (m 0 + 1) k) := by
    refine ⟨(continuous_const.matrix_mul continuous_id).measurable, ?_⟩
    have hs := padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) (m 0 + 1) k
      (rectangularMeasure ν (m 0 + 1) k) (leftMultiplier h u)⁻¹ 1
    simpa only [map_inv, hA, inv_one, map_one, Units.val_one, one_pow, div_one,
      one_smul, Matrix.mul_one] using hs
  have hy : MeasurePreserving
      (fun y : Matrix (Fin j) (Fin (m 1 + 1)) F =>
        y * (rightMultiplier h u).val)
      (rectangularMeasure ν j (m 1 + 1)) (rectangularMeasure ν j (m 1 + 1)) := by
    refine ⟨(continuous_id.matrix_mul continuous_const).measurable, ?_⟩
    have hs := padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) j (m 1 + 1)
      (rectangularMeasure ν j (m 1 + 1)) 1 (rightMultiplier h u)⁻¹
    simpa only [map_inv, hB, inv_one, inv_inv, map_one, Units.val_one, one_pow,
      div_one, one_smul, Matrix.one_mul] using hs
  exact hx.prod hy

/-- Total Bochner change of variables; it does not assert integrability. -/
theorem integral_rectangleChange {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j k : ℕ) (ν : AdditiveHaarMeasure F)
    (u : lowerBlockUnipotent h F) (φ : Rectangles m j k F → E) :
    (∫ z, φ (rectangleChange h j k u z) ∂rectangleMeasure F m j k ν) =
      ∫ z, φ z ∂rectangleMeasure F m j k ν :=
  (measurePreserving_rectangleChange F h j k ν u).integral_comp
    (rectangleChangeHomeomorph F h j k u).measurableEmbedding φ

/-- Actual integrability is equivalent in both directions, for arbitrary inputs. -/
theorem integrable_rectangleChange_iff {E : Type uE} [NormedAddCommGroup E]
    (j k : ℕ) (ν : AdditiveHaarMeasure F)
    (u : lowerBlockUnipotent h F) (φ : Rectangles m j k F → E) :
    Integrable (fun z => φ (rectangleChange h j k u z)) (rectangleMeasure F m j k ν) ↔
      Integrable φ (rectangleMeasure F m j k ν) :=
  (measurePreserving_rectangleChange F h j k ν u).integrable_comp_emb
    (rectangleChangeHomeomorph F h j k u).measurableEmbedding

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
