import Langlands.Representation.GodementJacquet.FunctionalEquationTransport
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
/-!
# Transport of full normalized matrix functional-equation data

The existing actual-data equivalence theorem proves the closed statement.
Its canonical p-adic specialization retains the supplied Fourier measure.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement glCoefficientModel_isOfWhittakerType matrixComparisonModelsTopology normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixFETransportGLBorel matrixFETransportGLMeasurable matrixFETransportLocalField matrixFETransportMeasurable matrixFETransportTopology matrixFETransportValuative matrixIntegral matrixIntegrand matrixRationalValues normalizedMatrixFunctionalEquationData_equiv whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues normalizedMatrixFunctionalEquationData_equiv whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixFETransportMeasurable : MeasurableSpace F := borel _
local instance matrixFETransportGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance matrixFETransportGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- Canonical p-adic specialization retaining the supplied Fourier measure. -/
theorem normalizedMatrixFunctionalEquationData_equiv
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (e : σ.Equiv τ) (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) :
    NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m ↔
      NormalizedMatrixFunctionalEquationData F ψ ν τ P PDual c m :=
  GodementJacquet.normalizedMatrixFunctionalEquationData_equiv
    (q := (⟨⟩ : LocalFieldData F).residueCardinality) (ψ := ψ) (ν := ν)
    (abv := normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (μ := generalLinearHaar F n) e

end Padic

end Langlands.AllField.GodementJacquet
