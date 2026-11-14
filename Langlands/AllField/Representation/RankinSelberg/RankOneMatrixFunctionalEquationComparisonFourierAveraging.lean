import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierAveraging
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAveraging
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
/-!
# Fourier-compatible averaging and conditional model functional equations

The averaging subgroup depends only on the original full-matrix test.
The same actual coefficient works with every supplied Fourier partner.
Original and inverse-transpose convergence remain hypotheses.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData averagedModelCoefficient averagedModelCoefficient_apply averagedModelCoefficient_paired_integrals averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel coefficientIota_averagedModelCoefficient comparisonAveragingBorelSpace comparisonAveragingLocalField comparisonAveragingMeasurableSpace comparisonAveragingSecondCountable comparisonAveragingSigmaCompact comparisonAveragingTopology comparisonAveragingValuativeRel exists_compactOpen_matrixTest_invariant exists_nhds_matrixTest_invariant fourierAveragingTopology instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 inverseTransposeOpenSubgroup inverseTransposeOpenSubgroup_toSubgroup iotaMatrixRationalValues isCompact_inverseTransposeOpenSubgroup jpssI2 jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_normalizedLeftAverage matrixIntegrand matrixRationalValues modelSetIntegral modelSetIntegralDual whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {n : ℕ}

/-- The preimage subgroup used by averaging is the image subgroup appearing
in actual Fourier covariance, because inverse transpose is involutive. -/
theorem inverseTransposeOpenSubgroup_toSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
    (inverseTransposeOpenSubgroup F K).toSubgroup =
      K.toSubgroup.map (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨GeneralLinear.inverseTranspose (n + 1) F g, hg, ?_⟩
    exact GeneralLinear.inverseTranspose_involutive (n + 1) F g
  · rintro ⟨k, hk, rfl⟩
    change GeneralLinear.inverseTranspose (n + 1) F
      (GeneralLinear.inverseTranspose (n + 1) F k) ∈ K
    rw [GeneralLinear.inverseTranspose_involutive]
    exact hk

end Langlands.AllField.GodementJacquet.Padic
