import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof
/-! Exact multiplicative Haar transport from scalars to one-by-one matrices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacterReduction
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear

universe uF

section Coordinates


end Coordinates

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_tateScalarEquiv_iff integral_tateScalarEquiv iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues tateScalarEquiv_measurePreserving tateTransportGLBorel tateTransportGLLocallyCompact tateTransportGLMeasurable tateTransportGLSecondCountable tateTransportLocalField tateTransportTopology tateTransportUnitsBorel tateTransportUnitsMeasurable tateTransportValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance tateTransportUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance tateTransportUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩
local instance tateTransportGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance tateTransportGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance tateTransportGLLocallyCompact (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance tateTransportGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)

/-- Both multiplicative Haar measures give the integral units mass one, so
the scalar isomorphism preserves them without a normalization factor. -/
theorem tateScalarEquiv_measurePreserving :
    MeasurePreserving (tateScalarEquiv F)
      (localMultiplicativeHaar F) (generalLinearHaar F 0) := by
  let e := tateScalarEquiv F
  let μ := localMultiplicativeHaar F
  let K := Conductor.levelOpenSubgroup F 0 0
  have hpre : e ⁻¹' (K : Set (Langlands.GeneralLinear 1 F)) =
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ) := by
    ext a
    change e a ∈ Conductor.levelSubgroup F 0 0 ↔ _
    rw [Conductor.levelSubgroup_zero]
    exact tateScalarEquiv_mem_integral F _ a
  have hm : μ.map e (K : Set (Langlands.GeneralLinear 1 F)) = 1 := by
    rw [Measure.map_apply (f := fun a => e a)
      e.continuous_toFun.measurable K.isOpen.measurableSet, hpre]
    exact localMultiplicativeHaar_integerUnits F
  refine ⟨e.continuous.measurable, ?_⟩
  exact ((Measure.haarMeasure_eq_iff
    (compactOpenPositive K (Conductor.isCompact_levelOpenSubgroup F 0 0))
    (μ.map e)).mpr hm).symm

/-- Integrability of every function transports with the canonical measures. -/
theorem integrable_tateScalarEquiv_iff (A : Langlands.GeneralLinear 1 F → ℂ) :
    Integrable (fun a => A (tateScalarEquiv F a))
      (localMultiplicativeHaar F) ↔
    Integrable A (generalLinearHaar F 0) :=
  (tateScalarEquiv_measurePreserving F).integrable_comp_emb
    (tateScalarEquiv F).toHomeomorph.measurableEmbedding

/-- Actual integrals, including the totalized nonintegrable case, transport. -/
theorem integral_tateScalarEquiv (A : Langlands.GeneralLinear 1 F → ℂ) :
    (∫ a, A (tateScalarEquiv F a) ∂localMultiplicativeHaar F) =
      ∫ g, A g ∂generalLinearHaar F 0 :=
  (tateScalarEquiv_measurePreserving F).integral_comp
    (tateScalarEquiv F).toHomeomorph.measurableEmbedding A

end Padic

end Langlands.AllField.GodementJacquet
