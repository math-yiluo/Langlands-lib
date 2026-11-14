import Langlands.Representation.GodementJacquet.RegularMatrixHaarDensity
import Langlands.AllField.Representation.GodementJacquet.RegularMatrixZetaOperator
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
/-! Cancellation of the determinant density on regular matrix functions. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff integral_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open scoped NNReal

universe uK



end Langlands.AllField.RankinSelberg.GLDeterminantDensity

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral exists_integral_regularMatrix_density exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues regularDensityBorel regularDensityGLBorel regularDensityGLMeasurable regularDensityLocalField regularDensityMeasurable regularDensitySecondCountable regularDensityT2 regularDensityTopology regularDensityValuation regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance regularDensityT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance regularDensitySecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance regularDensityMeasurable : MeasurableSpace F := borel _
local instance regularDensityBorel : BorelSpace F := ⟨rfl⟩
local instance regularDensityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance regularDensityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

/-- A single positive scalar compares all regular matrix functions, with
the determinant density cancelled by the actual integer zeta weight. -/
theorem exists_integral_regularMatrix_density (n : ℕ)
    (ν : AdditiveHaarMeasure F) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ),
        (∀ X, ¬ IsUnit X → f X = 0) →
        (c : ℂ) * (∫ g : GeneralLinear (n + 1) F,
          f g.val *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F n) =
          ∫ X, f X ∂rectangularMeasure ν (n + 1) (n + 1) := by
  obtain ⟨c, hc, hμ⟩ :=
    Langlands.AllField.RankinSelberg.GLDeterminantDensity.padic_exists_weightedRestriction_eq_generalLinearHaar
      F (⟨⟩ : LocalFieldData F) n (rectangularMeasure ν (n + 1) (n + 1))
  refine ⟨c, hc, ?_⟩
  intro f hf
  have h := GLDeterminantDensity.integral_matrixDeterminantPower
    (n + 1) (⟨⟩ : LocalFieldData F).normalizedAbsHom
    (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom
    (rectangularMeasure ν (n + 1) (n + 1)) f hf
  rw [hμ, integral_smul_nnreal_measure] at h
  have hw (g : GeneralLinear (n + 1) F) :
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        g ((n + 1 : ℕ) : ℂ) =
      (GLDeterminantDensity.matrixDeterminantPower (n + 1)
        (⟨⟩ : LocalFieldData F).normalizedAbsHom g.val : ℂ) := by
    change ((⟨⟩ : LocalFieldData F).normalizedAbs g.val.det : ℂ) ^
      ((n + 1 : ℕ) : ℂ) = _
    simp only [Complex.cpow_natCast,
      GLDeterminantDensity.matrixDeterminantPower, GLDeterminantDensity.forwardWeight, NNReal.coe_pow,
      Complex.ofReal_pow, Langlands.LocalFieldData.normalizedAbsHom_coe]
  simp_rw [hw]
  simpa only [NNReal.smul_def, Complex.real_smul, mul_comm] using h

end Langlands.AllField.GodementJacquet.Padic
