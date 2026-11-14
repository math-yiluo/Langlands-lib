import Langlands.Representation.GodementJacquet.FourierRegularRationalEquation
import Langlands.AllField.Representation.GodementJacquet.ContinuedMatrixCovariance
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalFourierRegularEquation
/-! # Shifted rational equations on Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData aestronglyMeasurable_dualParabolicIntegrand compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel continuedMatrixCovarianceBorel continuedMatrixCovarianceDisconnected continuedMatrixCovarianceGLBorel continuedMatrixCovarianceGLMeasurable continuedMatrixCovarianceLocalField continuedMatrixCovarianceMeasurable continuedMatrixCovarianceT2 continuedMatrixCovarianceTopology continuedMatrixCovarianceValuation convolutionExchangeBorel convolutionExchangeDisconnected convolutionExchangeGLBorel convolutionExchangeGLMeasurable convolutionExchangeLocalField convolutionExchangeMeasurable convolutionExchangeT2 convolutionExchangeTopology convolutionExchangeValuation determinantWeight_inv_inverseTranspose determinantWeight_locallyConstant determinantWeight_neg_dimension determinantWeight_shift_spectral determinantWeight_sub_spectral dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel dualWeightedRegularMatrixTest dualWeightedRegularMatrixTest_apply dualWeightedRegularMatrixTest_convolution_cross dualWeightedRegularMatrixTest_convolution_left dualWeightedRegularMatrixTest_convolution_right epsilonMonomial_shiftedMatrixMonomialUnit exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_integral_regularMatrix_density exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_regularMatrixZetaOperator_dual_sub exists_laurent_scalar_of_fourierRegular_cross exists_monomial_fourierRegular_inverseTranspose exists_monomial_scalar_of_fourierRegular_cross exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero fourierRegularEquationBorel fourierRegularEquationDisconnected fourierRegularEquationLocalField fourierRegularEquationMeasurable fourierRegularEquationT2 fourierRegularEquationTopology fourierRegularEquationValuation fourierRegularInverseTransposeZetaOperator fourierRegularInverseTransposeZetaOperator_apply fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs fourierRegularRationalBorel fourierRegularRationalDisconnected fourierRegularRationalGLBorel fourierRegularRationalGLMeasurable fourierRegularRationalLocalField fourierRegularRationalMeasurable fourierRegularRationalT2 fourierRegularRationalTopology fourierRegularRationalValuation generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaFourierMatrixCoefficientRationalPairing iotaFourierMatrixCoefficientRationalPairing_spec iotaFourierMatrixCoefficientRationalPairing_translate iotaMatrixRationalValues jpssI2 jpssI3 laurentComparisonBorel laurentComparisonDisconnected laurentComparisonGLBorel laurentComparisonGLMeasurable laurentComparisonLocalField laurentComparisonMeasurable laurentComparisonT2 laurentComparisonTopology laurentComparisonValuativeRel leftRightTranslate_mem_fourierRegularMatrixTests map_mulLeftMeasurableEquiv matrixCoefficientRationalPairing matrixCoefficientRationalPairing_spec matrixCoefficientRationalPairing_translate matrixFourierEquiv_translate_of_norm_one matrixIntegral matrixIntegral_eq_of_fourierRegular_inverseTranspose matrixIntegrand matrixRationalPairing_identity_of_fourierRegular_operator matrixRationalValues measurable_inverseTranspose_val monomialBorel monomialComparisonBorel monomialComparisonDisconnected monomialComparisonLocalField monomialComparisonMeasurable monomialComparisonT2 monomialComparisonTopology monomialComparisonValuativeRel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel normalizedFunctionalEquation_of_fourierRegular_operator rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem regularDensityBorel regularDensityGLBorel regularDensityGLMeasurable regularDensityLocalField regularDensityMeasurable regularDensitySecondCountable regularDensityT2 regularDensityTopology regularDensityValuation regularMatrixRationalValue_eval regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_inverseTranspose regularMatrixZetaOperator_inverseTranspose_cross regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs scalar_ne_zero_of_fourierRegular_comparison shiftedMatrixMonomialUnit span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicSelfDualMeasureExistsStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicSelfDualMeasureExists padicSquareFourierIntegral_crossExchange padicSquareFourierIntegral_transposeRight rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.LocalFactor

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance fourierRegularRationalT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance fourierRegularRationalDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance fourierRegularRationalMeasurable : MeasurableSpace F := borel _
local instance fourierRegularRationalBorel : BorelSpace F := ⟨rfl⟩
local instance fourierRegularRationalGLMeasurable (m : ℕ) :
    MeasurableSpace (GeneralLinear (m + 1) F) := borel _
local instance fourierRegularRationalGLBorel (m : ℕ) :
    BorelSpace (GeneralLinear (m + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abvF" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "μF" => generalLinearHaar F n

/-- The fixed scalar introduced by writing an unshifted monomial in the
normalized spectral parameter. -/
def shiftedMatrixMonomialUnit (n : ℕ) (c : ℂˣ) (k : ℤ) : ℂˣ :=
  c * spectralShiftUnit qF (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    (jpssShift n) ^ k

theorem epsilonMonomial_shiftedMatrixMonomialUnit
    (c : ℂˣ) (k : ℤ) (s : ℂ) :
    epsilonMonomial qF (shiftedMatrixMonomialUnit F n c k) k s =
      (c : ℂ) * spectralPoint qF (s + jpssShift n) ^ k := by
  simp only [epsilonMonomial, shiftedMatrixMonomialUnit, Units.val_mul,
    Units.val_zpow_eq_zpow_val, coe_spectralShiftUnit,
    spectralPoint_add (⟨⟩ : LocalFieldData F).residueCardinality_gt_one, mul_zpow]
  ring

/-- For a regular test and a continuous coefficient, every supplied actual
rational value agrees with the convergent integral at every parameter. -/
theorem regularMatrixRationalValue_eval
    (Φ : regularMatrixTests (K := F) (n + 1))
    (f : GeneralLinear (n + 1) F → ℂ) (hf : Continuous f)
    (R : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ.val f R) (s : ℂ) :
    R.denom.eval (spectralPoint qF s) ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint qF s) R =
        matrixIntegral F Φ.val (s + jpssShift n) f := by
  obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_of_hasCompactSupport F Φ.val f hf
    (hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right
  have hAR : HasRationalContinuation qF
      (fun s => matrixIntegral F Φ.val (s + jpssShift n) f) (laurentToRatFunc A) := by
    refine ⟨0, fun s _ => ?_⟩
    obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval
      (spectralUnit (Nat.zero_lt_one.trans
        (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s) A
    exact ⟨hd, (hA s).2.trans he.symm⟩
  have heq := hAR.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hR.2
  rw [← heq]
  obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s) A
  exact ⟨hd, he.trans (hA s).2.symm⟩

/-- An all-parameter unshifted operator equation gives the normalized
functional equation for every supplied pair of actual rational values. -/
theorem normalizedFunctionalEquation_of_fourierRegular_operator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd)
    (hFE : ∀ s : ℂ,
      fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) (ℓ : Module.Dual ℂ V) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ.val (matrixCoefficient ρ ℓ v) R)
    (hD : HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val)
      (coefficientIota (matrixCoefficient ρ ℓ v)) RDual) :
    NormalizedFunctionalEquation qF 1 1 1
      (shiftedMatrixMonomialUnit F n c k) 0 k R RDual := by
  have hf : Continuous (matrixCoefficient ρ ℓ v) :=
    ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp ℓ).continuous
  have hfι : Continuous (coefficientIota (matrixCoefficient ρ ℓ v)) :=
    hf.comp (GeneralLinear.continuous_inverseTranspose _ _)
  intro s _ _
  have hRe := (regularMatrixRationalValue_eval F ⟨Φ.val, Φ.property.1⟩
    (matrixCoefficient ρ ℓ v) hf R hR s).2
  have hDe := (regularMatrixRationalValue_eval F
    ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩
    (coefficientIota (matrixCoefficient ρ ℓ v)) hfι RDual hD (1 - s)).2
  simp only [Polynomial.eval_one, Units.val_one, one_pow, one_mul]
  rw [hRe, hDe, epsilonMonomial_shiftedMatrixMonomialUnit]
  have hshift : ((n + 1 : ℕ) : ℂ) - (s + jpssShift n) =
      (1 - s) + jpssShift n := by
    simp only [Nat.cast_add, Nat.cast_one, jpssShift]
    ring
  have he := matrixIntegral_eq_of_fourierRegular_inverseTranspose F ρ hρ hι ψ ν hsd
    (s + jpssShift n) ((c : ℂ) * spectralPoint qF (s + jpssShift n) ^ k)
    Φ (hFE _) v ℓ
  rw [hshift] at he
  exact he

/-- The actual chosen pairings obey the reflected rational identity on the
Fourier-regular subspace, with the same globally fixed shifted monomial. -/
theorem matrixRationalPairing_identity_of_fourierRegular_operator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd)
    (hFE : ∀ s : ℂ,
      fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) :
    RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat Φ.val v) =
      laurentToRatFunc (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k :
        LaurentCoefficients) * matrixCoefficientRationalPairing F ρ ℓ hRat Φ.val v := by
  apply NormalizedFunctionalEquation.rational_identity
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  exact normalizedFunctionalEquation_of_fourierRegular_operator F ρ hρ hι
    ψ ν hsd c k Φ hFE v ℓ _ _
    (matrixCoefficientRationalPairing_spec F ρ ℓ hRat Φ.val v)
    (iotaFourierMatrixCoefficientRationalPairing_spec F ψ ν hsd ρ ℓ hIotaRat Φ.val v)

end Langlands.AllField.GodementJacquet.Padic
