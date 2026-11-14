import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLFourierBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSingularNull
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
/-! # The actual Fourier exchange on unipotent times general linear groups -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight glFourierGLBorelSpace glFourierGLMeasurableSpace glFourierLocalField glFourierMeasurableSpace glFourierTopology glFourierValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff_full integral_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight_full padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos rectangularMeasure_ae_det_ne_zero rectangularMeasure_restrict_generalLinear singularNullBorelSpace singularNullLocalField singularNullMeasurableSpace singularNullPuncturedNhds singularNullSecondCountable singularNullSigmaCompact singularNullT2 singularNullTopology singularNullValuativeRel weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis

universe uF uH

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance glFourierMeasurableSpace : MeasurableSpace F := borel _
local instance glFourierGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance glFourierGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- Joint integrability with any s-finite auxiliary measure, on the full
additive matrix space and the unchanged general linear Haar measure. -/
theorem integrable_prod_generalLinearHaar_natWeight_iff_full
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val))
        (μH.prod (generalLinearHaar F n)) ↔
    Integrable A (μH.prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integrable_prod_generalLinearHaar_natWeight_iff F μH ν n A

/-- Full product-measure identity; the auxiliary measure and integrand do not
change the one normalization scalar. -/
theorem integral_prod_generalLinearHaar_natWeight_full
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    (∫ z : H × Langlands.GeneralLinear (n + 1) F,
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val)
        ∂μH.prod (generalLinearHaar F n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod (rectangularMeasure ν (n + 1) (n + 1)) := by
  simpa only [rectangularMeasure_restrict_generalLinear F ν (n + 1)] using
    integral_prod_generalLinearHaar_natWeight F μH ν n A

end Langlands.AllField.RankinSelberg.GLDeterminantDensity
