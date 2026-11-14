import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionMeasure
import Langlands.AllField.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockCoordinates
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRawKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentInvolution
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-! # Supplied-Haar transport for the reflected first rectangle -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation integrable_firstBlockRowChange_iff integral_firstBlockReflectedRectangle integral_firstBlockRowChange rectangularMeasure_map_firstBlockReflectedRectangle rectangularMeasure_map_firstBlockRowChange reflectionMeasureBorel reflectionMeasureCountable reflectionMeasureLocalField reflectionMeasureMatrixBorel reflectionMeasureMeasurable reflectionMeasureT2 reflectionMeasureTopology reflectionMeasureValuation
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding measurePreserving_reflectionQuotient reflectionQuotient_mem_determinantSlice setIntegral_determinantSlice_reflectionQuotient
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open scoped NNReal

universe uK uF uE

section Coordinates


end Coordinates

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance reflectionMeasureCountable : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance reflectionMeasureT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance reflectionMeasureMeasurable : MeasurableSpace F := borel _
local instance reflectionMeasureBorel : BorelSpace F := ⟨rfl⟩
local instance reflectionMeasureMatrixBorel (a q : ℕ) : BorelSpace (Matrix (Fin a) (Fin q) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin q → F))

variable (ν : AdditiveHaarMeasure F) {a q : ℕ} (v : GeneralLinear a F)

/-- Transpose, unsigned Weyl and negation retain the supplied scalar Haar;
left multiplication contributes exactly the inverse determinant power. -/
theorem rectangularMeasure_map_firstBlockReflectedRectangle :
    (rectangularMeasure ν q a).map (firstBlockReflectedRectangle v) =
      (((⟨⟩ : LocalFieldData F).determinantNorm a v : ℝ≥0) ^ q)⁻¹ •
        rectangularMeasure ν a q := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have : LocallyCompactSpace F := inferInstance
  have : ν.measure.IsNegInvariant := inferInstance
  have : (rectangularMeasure ν a q).IsNegInvariant := by
    change (Measure.pi (fun _ : Fin a => Measure.pi (fun _ : Fin q => ν.measure))).IsNegInvariant
    infer_instance
  have hT := GodementJacquet.measurePreserving_transpose_rectangularMeasure ν q a
  have hw : (⟨⟩ : LocalFieldData F).determinantNorm a (weylLong a F) = 1 := by
    apply Units.ext
    apply NNReal.eq
    exact abv_det_weylLong (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a
  have hL := padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) a q
    (rectangularMeasure ν a q) (weylLong a F * v) 1
  simp only [inv_one, map_one, Units.val_one, one_pow, div_one, Matrix.mul_one,
    map_mul, hw, one_mul] at hL
  have hm : Measurable (fun X : Matrix (Fin a) (Fin q) F =>
      (weylLong a F * v).val * X) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hfun : firstBlockReflectedRectangle v =
      (fun X : Matrix (Fin a) (Fin q) F => -X) ∘
        ((fun X => (weylLong a F * v).val * X) ∘
          (GodementJacquet.transposeMeasurableEquiv q a)) := by
    funext z
    simp [firstBlockReflectedRectangle, Matrix.neg_mul, GodementJacquet.transposeMeasurableEquiv]
  rw [hfun, ← Measure.map_map measurable_neg (hm.comp hT.measurable),
    ← Measure.map_map hm hT.measurable, hT.map_eq, hL,
    Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_neg_eq_self]

/-- Bochner substitution with the exact supplied-Haar determinant factor. -/
theorem integral_firstBlockReflectedRectangle
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Matrix (Fin a) (Fin q) F → E) :
    (∫ z, φ (firstBlockReflectedRectangle v z) ∂rectangularMeasure ν q a) =
      ((((⟨⟩ : LocalFieldData F).determinantNorm a v : ℝ≥0) ^ q)⁻¹ : ℝ≥0) •
        ∫ X, φ X ∂rectangularMeasure ν a q := by
  change (∫ z, φ ((firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv z)
    ∂rectangularMeasure ν q a) = _
  rw [← integral_map_equiv (firstBlockReflectedRectangleHomeomorph v).toMeasurableEquiv φ]
  change (∫ X, φ X ∂(rectangularMeasure ν q a).map (firstBlockReflectedRectangle v)) = _
  rw [rectangularMeasure_map_firstBlockReflectedRectangle, integral_smul_nnreal_measure]

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
