import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement
import Langlands.AllField.Representation.RankinSelberg.GammaFactor
import Langlands.AllField.Representation.RankinSelberg.PairLFactor
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Inverse-transpose substitution in transformed matrix integrals

For a group measure preserved by the inverse transpose `ι g = (g⁻¹)ᵀ`, the
matrix integrand of `coefficientIota f` composed with `ι` is
`g ↦ Φ (ι g) * f g * |det g|^(-s)`. Hence convergence and the value of the
transformed matrix integral are those of this substituted integrand.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF

section General



end General

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F]

/-- The canonical normalized group Haar measure is preserved by inverse transpose. -/
theorem generalLinearHaar_measurePreserving_inverseTranspose [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
    haveI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F)
      (generalLinearHaar F n) (generalLinearHaar F n) := by
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  exact (generalLinearHaarSymmetries F n).2.1

end Padic

end Langlands.AllField.GodementJacquet
