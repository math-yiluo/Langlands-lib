import Langlands.Representation.GodementJacquet.TateMatrixAnalyticData
import Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.AllField.Representation.GodementJacquet.TateScalarMellin
import Langlands.AllField.Representation.GodementJacquet.TateScalarTransport
/-! Actual rank-one matrix analytics from a proved scalar character action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding MatrixUnitValueStatement matrixUnitValue scalarMellinAnalyticData_finiteFunction
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def finiteFunctionShellSeries iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice rankOneCharacterReduction rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear

universe uF uV

section Algebra


end Algebra

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData exists_biSmoothCoefficient_ne_zero exists_matrixIntegral_one exists_tateCharacterCoefficient exists_tateIotaMatrixAnalyticAssertions exists_tateMatrixAnalyticAssertions instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_tateScalarEquiv_iff integral_tateScalarEquiv iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues tateAnalyticsGLBorel tateAnalyticsGLMeasurable tateAnalyticsLocalField tateAnalyticsTopology tateAnalyticsUnitsBorel tateAnalyticsUnitsMeasurable tateAnalyticsValuation tateCharacter_mellinAnalyticData tateHasShiftedRationalValue_iff tateIotaMatrixRationalValues_eq_scalar tateMatrixIntegral_eq_scalar tateMatrixIntegrand_eq_scalar tateMatrixRationalValues_eq_scalar tateMatrix_characterConverges tateScalarEquiv_measurePreserving tateTransportGLBorel tateTransportGLLocallyCompact tateTransportGLMeasurable tateTransportGLSecondCountable tateTransportLocalField tateTransportTopology tateTransportUnitsBorel tateTransportUnitsMeasurable tateTransportValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue scalarMellinAnalyticData_finiteFunction whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance tateAnalyticsUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance tateAnalyticsUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩
local instance tateAnalyticsGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance tateAnalyticsGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

/-- The scalar character has actual uniform Mellin analytic data. -/
theorem tateCharacter_mellinAnalyticData (χ : Quasicharacter F) :
    ScalarMellinAnalyticData (⟨⟩ : LocalFieldData F).residueCardinality
      (⟨⟩ : LocalFieldData F).normalizedAbs (localMultiplicativeHaar F)
      (fun a => (χ a : ℂ)) 1 :=
  scalarMellinAnalyticData_finiteFunction F (⟨⟩ : LocalFieldData F) 1 zero_lt_one
    (fun a => (χ a : ℂ)) (Units.continuous_val.comp χ.continuous)
    (tateCharacter_translationFinite χ)

/-- Scalar and matrix integrands agree after absorbing the coefficient at one
into the genuine scalar test. -/
theorem tateMatrixIntegrand_eq_scalar (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear 1 F → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F) (s : ℂ) :
    (fun a => GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Φ s f
      (tateScalarEquiv F a)) =
    scalarMellinIntegrand (⟨⟩ : LocalFieldData F).normalizedAbs
      (fun a => (χ a : ℂ)) 1 (f 1 • tateScalarTest F Φ) s := by
  funext a
  rw [GodementJacquet.matrixIntegrand, hf]
  simp [tateScalarEquiv, scalarMellinIntegrand, tateScalarTest_scalar,
    determinantWeight, determinant, scalar, Matrix.GeneralLinearGroup.coe_scalar,
    normalizedAbsoluteValue, mul_comm, mul_left_comm, mul_assoc]

/-- Equality of the actual integrals uses the exact canonical Haar transport. -/
theorem tateMatrixIntegral_eq_scalar (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear 1 F → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F) (s : ℂ) :
    matrixIntegral F Φ s f =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs
        (localMultiplicativeHaar F) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F Φ) s := by
  change (∫ g, GodementJacquet.matrixIntegrand _ Φ s f g ∂_) = _
  rw [← integral_tateScalarEquiv F, tateMatrixIntegrand_eq_scalar F χ f hf]
  rfl

/-- One convergence half-plane works for all tests and scalar multiples of
this character, before a coefficient family is specified. -/
theorem tateMatrix_characterConverges (χ : Quasicharacter F) :
    ∃ c : ℝ, ∀ Φ : MatrixTestFunction 0 F,
      ∀ f : Langlands.GeneralLinear 1 F → ℂ,
      (∀ g, f g = f 1 * (χ (determinant g) : ℂ)) →
      ∀ s : ℂ, c < s.re → MatrixConverges F Φ (s + jpssShift 0) f := by
  obtain ⟨c, hc⟩ := (tateCharacter_mellinAnalyticData F χ).1
  refine ⟨c, fun Φ f hf s hs => ?_⟩
  apply (integrable_tateScalarEquiv_iff F _).mp
  rw [tateMatrixIntegrand_eq_scalar F χ f hf]
  simpa [jpssShift] using hc (f 1 • tateScalarTest F Φ) s hs

/-- The rank-one shift is zero, and genuine convergence is already proved. -/
theorem tateHasShiftedRationalValue_iff (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear 1 F → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F) (R : RationalFunctions) :
    HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (generalLinearHaar F 0) Φ f R ↔
    HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
      (scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs
        (localMultiplicativeHaar F) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F Φ)) R := by
  have heq : (fun s => GodementJacquet.matrixIntegral
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (generalLinearHaar F 0) Φ (s + jpssShift 0) f) =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs
        (localMultiplicativeHaar F) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F Φ) := by
    funext s
    simpa [jpssShift, matrixIntegral] using tateMatrixIntegral_eq_scalar F χ f hf Φ s
  unfold HasShiftedRationalValue
  rw [heq]
  exact and_iff_right (by
    obtain ⟨c, hc⟩ := tateMatrix_characterConverges F χ
    exact ⟨c, hc Φ f hf⟩)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A genuine coefficient equal to the character, obtained by normalizing a
nonzero smooth coefficient at the identity. -/
theorem exists_tateCharacterCoefficient [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ f : biSmoothMatrixCoefficients σ, ∀ g, f.val g = (χ (determinant g) : ℂ) := by
  obtain ⟨ℓ, v, h⟩ := exists_biSmoothCoefficient_ne_zero F σ hσ
  let f : biSmoothMatrixCoefficients σ :=
    (ℓ.val v.val)⁻¹ • ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩
  refine ⟨f, fun g => ?_⟩
  change (ℓ.val v.val)⁻¹ * ℓ.val (σ g v.val) = _
  rw [hact, map_smul, smul_eq_mul]
  field_simp

/-- Matrix and scalar rational-value families are equal before taking any span. -/
theorem tateMatrixRationalValues_eq_scalar [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    matrixRationalValues F σ =
      scalarMellinRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
        (⟨⟩ : LocalFieldData F).normalizedAbs (localMultiplicativeHaar F)
        (fun a => (χ a : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨Φ, f, hR⟩
    exact ⟨f.val 1 • tateScalarTest F Φ,
      (tateHasShiftedRationalValue_iff F χ f.val (tateCoefficient_eq σ χ hact f) Φ R).mp hR⟩
  · rintro ⟨φ, hR⟩
    obtain ⟨f, hf⟩ := exists_tateCharacterCoefficient F σ χ hσ hact
    let Φ : MatrixTestFunction 0 F :=
      Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F) φ
    have hf1 : f.val 1 = 1 := by simp [hf]
    have htest : f.val 1 • tateScalarTest F Φ = φ := by
      rw [hf1, one_smul]
      exact (Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F)).left_inv φ
    refine ⟨Φ, f, (tateHasShiftedRationalValue_iff F χ f.val
      (tateCoefficient_eq σ χ hact f) Φ R).mpr ?_⟩
    rwa [htest]

/-- Uniform matrix convergence, rationality and a normalized generator follow
from the scalar Mellin theorem and the attained unit value. -/
theorem exists_tateMatrixAnalyticAssertions [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ P : Polynomial ℂ, MatrixAnalyticAssertions F σ P := by
  have hdata := tateCharacter_mellinAnalyticData F χ
  have hvalues := tateMatrixRationalValues_eq_scalar F σ χ hσ hact
  have hden : HasCommonDenominator (matrixRationalValues F σ) := by
    rw [hvalues]
    exact hdata.2.2
  obtain ⟨P, hP⟩ := normalizedGeneratorExistence (matrixRationalValues F σ) hden
    (Submodule.subset_span (one_mem_matrixRationalValues F σ hσ))
  refine ⟨P, ?_, ?_, hP⟩
  · obtain ⟨c, hc⟩ := tateMatrix_characterConverges F χ
    exact ⟨c, fun Φ f => hc Φ f.val (tateCoefficient_eq σ χ hact f)⟩
  · intro Φ f
    obtain ⟨R, hR⟩ := hdata.2.1 (f.val 1 • tateScalarTest F Φ)
    exact ⟨R, (tateHasShiftedRationalValue_iff F χ f.val
      (tateCoefficient_eq σ χ hact f) Φ R).mpr hR⟩

/-- The transformed value family is exactly the inverse-character Mellin
family, with the same Haar measure and spectral weight. -/
theorem tateIotaMatrixRationalValues_eq_scalar [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    iotaMatrixRationalValues F σ =
      scalarMellinRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
        (⟨⟩ : LocalFieldData F).normalizedAbs (localMultiplicativeHaar F)
        (fun a => ((χ⁻¹) a : ℂ)) 1 := by
  change GodementJacquet.iotaMatrixRationalValues _ _ _ σ = _
  rw [iotaMatrixRationalValues_eq_comp_inverseTranspose]
  exact tateMatrixRationalValues_eq_scalar F
    (σ.comp (inverseTranspose 1 F).toMonoidHom) χ⁻¹
    (isSmooth_comp _ (continuous_inverseTranspose _ _) hσ)
    (tateInverseTranspose_action σ χ hact)

/-- Transformed convergence, rationality and normalized generation are
transported from the actual inverse-transpose pullback. -/
theorem exists_tateIotaMatrixAnalyticAssertions [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (χ : Quasicharacter F) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ PDual : Polynomial ℂ, IotaMatrixAnalyticAssertions F σ PDual := by
  obtain ⟨PDual, hPDual⟩ := exists_tateMatrixAnalyticAssertions F
    (σ.comp (inverseTranspose 1 F).toMonoidHom) χ⁻¹
    (isSmooth_comp _ (continuous_inverseTranspose _ _) hσ)
    (tateInverseTranspose_action σ χ hact)
  exact ⟨PDual,
    (iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose _ _ _ PDual).mpr hPDual⟩

end Padic

end Langlands.AllField.GodementJacquet
