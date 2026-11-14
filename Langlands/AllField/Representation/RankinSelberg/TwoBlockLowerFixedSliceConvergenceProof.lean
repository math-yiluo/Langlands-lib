import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.QuotientTorusEnvelope
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity
/-! # Absolute convergence on each Section 4.7 lower determinant slice -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice quotientIwasawaIntegration rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding blockRotation_inv_mul_diagonal coefficient_locallyConstant exists_partialSection_diagonal_bounds exists_partialSection_diagonal_compact_bounds exists_partialSection_rotated_diagonal_compact_bounds exists_partialSection_rotated_torus_compact_bounds groupIntegrand groupIntegrand_def groupIntegrand_locallyConstant groupIntegrand_lowerBlockUnipotent_mul integrand integrand_continuous integrand_locallyConstant integrand_measurable integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_diagonal partialSection_locallyConstant partialSection_lowerBlockUnipotent_mul partialSection_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_locallyConstant scalarSection_lowerBlockUnipotent_mul sectionEval_locallyConstant sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding blockRotation_inv_mul_torus compatible_measure_data determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le diagonalDensity_nonneg exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_integrand_torus_majorant exists_rotated_section_growth exists_section_growth exists_standard_functional_growth exists_summable_integrand_majorant instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrable_lowerMeasure_iff integral_lowerMeasure integrand_standard_mk isEntryBounded_torus lowerMeasure lowerMeasure_restrict measureTransportFieldT2 measureTransportFieldTopology measureTransportFieldValuation measureTransportGeneralLinearGroup measureTransportGeneralLinearLocallyCompact measureTransportGeneralLinearSecondCountable measureTransportLocalField normalizedAbs_uniformizer_zpow sigmaFinite_lowerMeasure torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice

universe uF uV uW

/-- Fixed-slice absolute convergence of the actual lower integrand, with the
prescribed compatible quotient measures and supplied opposite-twist data. -/
theorem twoBlockLowerFixedSliceConvergence :
    TwoBlockLowerFixedSliceConvergenceStatement.{uF, uV, uW} := by
  intro F _ _ _ _
  dsimp only
  let := (⟨⟩ : LocalFieldData F).fieldT2
  let := (⟨⟩ : LocalFieldData F).secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν t m h
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace (GeneralLinear (t + 1) F) := borel _
  let : BorelSpace (GeneralLinear (t + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (t + 1) F) := borel _
  let : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient t F) := borel _
  let : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
  let : MeasurableSpace (LowerQuotient h F) := borel _
  let : BorelSpace (LowerQuotient h F) := ⟨rfl⟩
  obtain ⟨hN, hmeasure⟩ := compatible_measure_data F h
  refine ⟨hN, ?_⟩
  let := hN
  refine ⟨hmeasure.1, hmeasure.2, ?_⟩
  intro V _ _ π hπ lambda W _ _ τ hτ ell
  have hjlt : m 1 < t := by
    have hh : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    omega
  let j : Fin t := ⟨m 1, hjlt⟩
  obtain ⟨C, hC⟩ :=
    exists_summable_integrand_majorant F h ψ ν π hπ lambda τ hτ ell j rfl
  refine ⟨C, fun u hu νN hνN f Wtest Φ k => ?_⟩
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let E : LowerQuotient h F → ℂ := integrand ellu f Wtest.val Φ ν.val
  have hE : Measurable E :=
    integrand_measurable ellu f π hπ.1.1 lambda Wtest Φ ν.val
  have hEs : Measurable (fun q => E ((lowerToStandard h F).symm q)) :=
    hE.comp (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  obtain ⟨A, _, hsum, hbound⟩ := hC u hu f Wtest Φ
  have hEst : Integrable (fun q => E ((lowerToStandard h F).symm q)) νN := by
    apply Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F (⟨⟩ : LocalFieldData F) t νN hνN
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (uniformizerUnit_isUniformizingElement F) _ hEs A _ hsum
    intro lam k hk
    exact hbound lam k ((mem_integralOpen F k).mpr
      ((Conductor.mem_integralSubgroup _ t k).mp hk))
  have hslice := hEst.restrict
    (s := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k)
  exact ⟨hE, (integrable_lowerMeasure_iff F h νN E k).mpr hslice, hslice,
    integral_lowerMeasure F h νN E k,
    integral_lowerMeasure F h νN (fun z => ‖E z‖) k⟩

end Langlands.AllField.RankinSelberg
