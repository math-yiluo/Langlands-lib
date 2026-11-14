import Langlands.Representation.GodementJacquet.SupercuspidalMatrixAssembly
import Langlands.AllField.Representation.GodementJacquet.MatrixDenominatorCancellation
import Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixRationality
/-! # Supercuspidal matrix analytic data from the raw monomial equation -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding HasMatrixMonomialFunctionalEquation IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData SupercuspidalMatrixRationalityData centralMatrixRationalityBorelSpace centralMatrixRationalityLocalField centralMatrixRationalityMeasurableSpace centralMatrixRationalityT2Space centralMatrixRationalityTopology centralMatrixRationalityValuativeRel compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_shift_spectral exists_biSmoothCoefficient_ne_zero exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_matrixIntegral_quotient exists_laurent_of_matrix_geometric_clearings exists_matrixIntegral_one exists_shiftedRationalValue_of_scalarSaturation exists_supercuspidalMatrixRationalityData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixAnalyticAssertions_succBlocks_iff iotaMatrixRationalValues jpssI2 jpssI3 laurentEval_matrixGeometricDenominator matrixAnalyticAssertions_reversedInverseTransposeBlocks matrixGeometricCoefficient matrixGeometricCoefficient_reflected_product matrixGeometricCoefficient_reflected_product_ne_one matrixGeometricDenominator matrixGeometricDenominator_ne_zero matrixIntegral matrixIntegrand matrixRationalValues matrixUniformizer matrixUniformizer_det_abs_lt_one matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation normalizedMatrixFunctionalEquationData_of_supercuspidal_of_monomial one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues supercuspidalMatrixAssemblyBorel supercuspidalMatrixAssemblyGLBorel supercuspidalMatrixAssemblyGLMeasurable supercuspidalMatrixAssemblyLocalField supercuspidalMatrixAssemblyMeasurable supercuspidalMatrixAssemblyT2 supercuspidalMatrixAssemblyTopology supercuspidalMatrixAssemblyTotallyDisconnected supercuspidalMatrixAssemblyValuation supercuspidalMatrixRationalityBorelSpace supercuspidalMatrixRationalityLocalField supercuspidalMatrixRationalityMeasurableSpace supercuspidalMatrixRationalityTopology supercuspidalMatrixRationalityValuativeRel twoBlockReversalGLBorel twoBlockReversalGLMeasurable twoBlockReversalLocalField twoBlockReversalTopology twoBlockReversalValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData determinantNorm_ker_sup_center_finiteIndex exists_centralCharacter_compactScalarSupport hasCompactSupport_determinantUnit_coefficient inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue oneBlockDeterminantUnitHomeomorph whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.LocalFactor
open Langlands.AllField.LocalFactor

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance supercuspidalMatrixAssemblyT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance supercuspidalMatrixAssemblyMeasurable : MeasurableSpace F := borel _
local instance supercuspidalMatrixAssemblyBorel : BorelSpace F := ⟨rfl⟩
local instance supercuspidalMatrixAssemblyTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance supercuspidalMatrixAssemblyGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance supercuspidalMatrixAssemblyGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The raw Fourier and monomial equation, without convergence, rational
existence or normalized-generator assertions. Fourier witnesses precede every
coefficient and both actual continuation guards are retained. -/
def HasMatrixMonomialFunctionalEquation
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (c : ℂˣ) (m : ℤ) : Prop :=
  ∀ Φ : MatrixTestFunction n F, ∃ ΦHat : MatrixTestFunction n F,
    MatrixFourierPair F ψ ν Φ ΦHat ∧
    ∀ f : biSmoothMatrixCoefficients ρ, ∀ R RDual : RationalFunctions,
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (generalLinearHaar F n) Φ f.val R →
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (generalLinearHaar F n) ΦHat (coefficientIota f.val) RDual →
      NormalizedFunctionalEquation (⟨⟩ : LocalFieldData F).residueCardinality
        1 1 1 c 0 m R RDual

/-- Every actual original continuation is Laurent once the raw monomial
equation is supplied. Rational uniqueness transfers the common clearing to
the continuation specified in the conclusion. -/
theorem SupercuspidalMatrixRationalityData.exists_laurent_value
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {ω c : ℂˣ} {m : ℤ}
    (hRat : SupercuspidalMatrixRationalityData F ρ ω)
    {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F}
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m)
    (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients ρ)
    {R : RationalFunctions}
    (hR : HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (generalLinearHaar F n) Φ f.val R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  obtain ⟨R₀, hR₀, hD⟩ := hRat.2.2.1 Φ f
  have huniq := hR₀.2.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hR.2
  subst R₀
  obtain ⟨ΦHat, _, hpair⟩ := hFE Φ
  obtain ⟨RDual, hRDual, hE⟩ := hRat.2.2.2 ΦHat f
  exact exists_laurent_of_matrix_geometric_clearings F (matrixUniformizer F n).val
    (matrixUniformizer_det_abs_lt_one F n) ω c m hD hE
    (hpair f R RDual hR hRDual)

/-- Fourier surjectivity covers every dual test. Reflecting the raw rational
identity transports the original Laurent value to its actual dual value. -/
theorem SupercuspidalMatrixRationalityData.exists_laurent_iota_value
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {ω c : ℂˣ} {m : ℤ}
    (hRat : SupercuspidalMatrixRationalityData F ρ ω)
    {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F}
    (hsd : IsSelfDual ψ ν)
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m)
    (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients ρ)
    {RDual : RationalFunctions}
    (hRDual : HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (generalLinearHaar F n) Φ (coefficientIota f.val) RDual) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = RDual := by
  let T := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd
  let Φ₀ := T.symm Φ
  obtain ⟨ΦHat, hFourier, hpair⟩ := hFE Φ₀
  have hΦHat : ΦHat = Φ := by
    apply Hecke.TestFunction.ext
    intro x
    calc
      ΦHat x = rectangularFourierIntegral ψ ν Φ₀ x := (hFourier x).2
      _ = T Φ₀ x := (rectangularFourierEquiv_apply ψ ν _ _ hsd Φ₀ x).symm
      _ = Φ x := by rw [LinearEquiv.apply_symm_apply]
  subst ΦHat
  obtain ⟨R, hR, _⟩ := hRat.2.2.1 Φ₀ f
  obtain ⟨A, hA⟩ := hRat.exists_laurent_value F hFE Φ₀ f hR
  have hid := (hpair f R RDual hR hRDual).rational_identity
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  let δ := spectralReflectionUnit (Nat.zero_lt_one.trans
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
  refine ⟨laurentReciprocal δ ((laurentMonomialUnit c m : LaurentCoefficients) * A), ?_⟩
  rw [laurentToRatFunc_reciprocal, map_mul, hA, ← hid, RationalReflection.subst_subst]

/-- Actual irreducible supercuspidality supplies all analytic and generator
assertions once the raw Fourier monomial functional equation is known. -/
theorem normalizedMatrixFunctionalEquationData_of_supercuspidal_of_monomial
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (c : ℂˣ) (m : ℤ)
    (hFE : HasMatrixMonomialFunctionalEquation F ψ ν ρ c m) :
    NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c m := by
  let := hi
  let : Nontrivial V := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)) ρ.asModule
  obtain ⟨ω, hRat⟩ := exists_supercuspidalMatrixRationalityData F ρ hρ hi
  refine ⟨⟨hRat.1, ?_, ?_⟩, ⟨hRat.2.1, ?_, ?_⟩, hFE⟩
  · intro Φ f
    obtain ⟨R, hR, _⟩ := hRat.2.2.1 Φ f
    exact ⟨R, hR⟩
  · apply (isNormalizedGenerator_iff _ _).2
    refine ⟨by simp, ?_, ?_⟩
    · rintro R ⟨Φ, f, hR⟩
      simpa using hRat.exists_laurent_value F hFE Φ f hR
    · simpa only [Langlands.AllField.GodementJacquet.Padic.matrixRationalValues, map_one, inv_one] using
        mem_zetaSpan (one_mem_matrixRationalValues F ρ hρ.1.1)
  · intro Φ f
    obtain ⟨R, hR, _⟩ := hRat.2.2.2 Φ f
    exact ⟨R, hR⟩
  · apply (isNormalizedGenerator_iff _ _).2
    refine ⟨by simp, ?_, ?_⟩
    · rintro R ⟨Φ, f, hR⟩
      simpa using hRat.exists_laurent_iota_value F hsd hFE Φ f hR
    · simpa only [Langlands.AllField.GodementJacquet.Padic.iotaMatrixRationalValues, map_one, inv_one] using
        mem_zetaSpan (one_mem_iotaMatrixRationalValues F ρ hρ.1.1)

end Langlands.AllField.GodementJacquet.Padic
