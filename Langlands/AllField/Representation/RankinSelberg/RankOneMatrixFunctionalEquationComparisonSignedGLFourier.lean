import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLFourierBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitFourier
/-! # The actual signed Fourier exchange on unipotent times general linear groups -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight generalLinear_signedUnipotentMatrixFourier_exchange glFourierGLBorelSpace glFourierGLMeasurableSpace glFourierLocalField glFourierMeasurableSpace glFourierTopology glFourierValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_generalLinear_signedUnipotentMatrixFourierDualKernel integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel integrable_prod_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff_full integral_generalLinearHaar_natWeight integral_generalLinear_signedUnipotentMatrixFourierDualKernel integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel integral_prod_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight_full padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos rectangularMeasure_ae_det_ne_zero rectangularMeasure_restrict_generalLinear signedGLFourierBorelSpace signedGLFourierGLBorelSpace signedGLFourierGLMeasurableSpace signedGLFourierGLSecondCountable signedGLFourierLocalField signedGLFourierMeasurableSpace signedGLFourierNBorelSpace signedGLFourierNLocallyCompact signedGLFourierNMeasurableSpace signedGLFourierNSecondCountable signedGLFourierT2 signedGLFourierTopology signedGLFourierTotallyDisconnected signedGLFourierValuativeRel signedUnipotentGeneralLinearFourierDualKernel signedUnipotentGeneralLinearFourierOriginalKernel singularNullBorelSpace singularNullLocalField singularNullMeasurableSpace singularNullPuncturedNhds singularNullSecondCountable singularNullSigmaCompact singularNullT2 singularNullTopology singularNullValuativeRel weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentMatrixFourierKernel_fixed signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedUnipotentMatrixFourier_exchange
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis

universe uF uH

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedGLFourierT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance signedGLFourierMeasurableSpace : MeasurableSpace F := borel _
local instance signedGLFourierBorelSpace : BorelSpace F := ⟨rfl⟩
local instance signedGLFourierGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance signedGLFourierGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance signedGLFourierGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance signedGLFourierNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).upperUnipotentLocallyCompactSpace (n + 1)
local instance signedGLFourierNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedGLFourierNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance signedGLFourierNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

local instance signedGLFourierTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The actual dual Fourier orbit kernel with the natural GL determinant weight. -/
def signedUnipotentGeneralLinearFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (z : upperUnipotent (n + 1) F ×
      Langlands.GeneralLinear (n + 1) F) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- The original orbit kernel with the identical natural GL determinant weight. -/
def signedUnipotentGeneralLinearFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (z : upperUnipotent (n + 1) F ×
      Langlands.GeneralLinear (n + 1) F) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (z.1, z.2.val)

/-- Actual inverse-transpose/Weyl dual kernel convergence on N × GL, without
any invertible-support premise on the Fourier transform of Φ. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    Integrable (signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (generalLinearHaar F n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F n) ν n _).2
      (integrable_signedUnipotentMatrixFourierDualKernel F ψ ν hsd n Φ Ψ A q ha hΨ)

/-- Actual original kernel convergence on N × GL, from invertible support of
Φ and no additional support premise on Ψ. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    Integrable (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (generalLinearHaar F n)) := by
  exact (integrable_prod_generalLinearHaar_natWeight_iff_full F
    (unipotentHaar F n) ν n _).2
      (integrable_signedUnipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ)

/-- Each actual dual product integral has the same inverse scalar as every
other weighted GL integral, with no test-dependent normalization. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    (∫ z, signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F n) ν n _

/-- The original product integral uses exactly the same normalization. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    (∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ z
        ∂(unipotentHaar F n).prod
          (rectangularMeasure ν (n + 1) (n + 1)) :=
  integral_prod_generalLinearHaar_natWeight_full F (unipotentHaar F n) ν n _

/-- Actual weighted Fourier exchange on N × GL; both product integrabilities
are proved and the identical normalization scalars cancel. -/
theorem generalLinear_signedUnipotentMatrixFourier_exchange
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    Integrable (signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (generalLinearHaar F n)) ∧
    Integrable (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (generalLinearHaar F n)) ∧
    (∫ z, signedUnipotentGeneralLinearFourierDualKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
    ∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n) := by
  refine ⟨integrable_generalLinear_signedUnipotentMatrixFourierDualKernel
    F ψ ν hsd n Φ Ψ A q ha hΨ,
    integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel
    F ψ ν hsd n Φ Ψ hΦ, ?_⟩
  rw [integral_generalLinear_signedUnipotentMatrixFourierDualKernel F ψ ν n Φ Ψ,
    integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel F ψ ν n Φ Ψ,
    (signedUnipotentMatrixFourier_exchange F ψ ν hsd n Φ Ψ hΦ A q ha hΨ).2.2]

end Langlands.AllField.RankinSelberg.GLDeterminantDensity
