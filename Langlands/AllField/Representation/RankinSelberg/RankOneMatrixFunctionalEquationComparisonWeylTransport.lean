import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! # Actual Weyl substitution for matrix integrals and their rational values -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker

universe uF

section LeftTranslation



end LeftTranslation

section WeylTranslation



end WeylTranslation

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixComparisonWeylGLBorel matrixComparisonWeylGLMeasurable matrixComparisonWeylLocalField matrixComparisonWeylTopology matrixComparisonWeylValuation matrixConverges_weylTranslate_dualFunction_iff matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData hasShiftedRationalValue_weylTranslate_dualFunction_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixConverges_weylTranslate_dualFunction_iff matrixIntegral matrixIntegral_weylTranslate_dualFunction matrixIntegrand matrixRationalValues shiftedConvergesOnRight_weylTranslate_dualFunction_iff whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixComparisonWeylGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance matrixComparisonWeylGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- Weyl convergence transport for the actual canonical p-adic matrix integral. -/
theorem matrixConverges_weylTranslate_dualFunction_iff
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) :
    MatrixConverges F (matrixWeylTranslate n Φ) s (dualFunction n f) ↔
      MatrixConverges F Φ s (coefficientIota f) :=
  GodementJacquet.matrixConverges_weylTranslate_dualFunction_iff
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F n) Φ s f

end Padic

end Langlands.AllField.GodementJacquet
