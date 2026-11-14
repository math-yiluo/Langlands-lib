import Langlands.Representation.GodementJacquet.SupercuspidalMatrixPairingExtension
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffOutputSpan
/-! # Extending Fourier-regular pairing identities to arbitrary tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel compactMatrixSmoothing_pairing conjugateSupercuspidalCutoffGroupTest conjugateSupercuspidalCutoffGroupTest_apply conjugateSupercuspidalCutoffGroupTest_conjugate conjugateSupercuspidalCutoffGroupTest_eq_zero determinantWeight_locallyConstant determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_smoothFunctional_ne_zero extensionBorel extensionDisconnected extensionGLBorel extensionGLMeasurable extensionLocalField extensionMeasurable extensionT2 extensionTopology extensionValuativeRel fourierRegularMatrixPairingRestriction fourierRegularMatrixPairingRestriction_apply generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integratedConjugateSupercuspidalCutoff_conjugate integratedConjugateSupercuspidalCutoff_ne_zero iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixPairing_eq_of_fourierRegular matrixPairing_eq_zero_of_fourierRegular matrixRationalValues nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel outputSpanGLBorel outputSpanGLMeasurable outputSpanLocalField outputSpanTopology outputSpanValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation smoothingBorel smoothingDisconnected smoothingGLBorel smoothingGLMeasurable smoothingLocalField smoothingMeasurable smoothingT2 smoothingTopology smoothingValuativeRel supercuspidalConjugateMatrixSmoothing supercuspidalConjugateMatrixSmoothing_eq_integratedAction supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalConjugateMatrixSmoothing_pairing supercuspidalCutoffGroupTest supercuspidalCutoffGroupTest_apply supercuspidalCutoffOutputSpan supercuspidalCutoffOutputSpan_apply_mem supercuspidalCutoffOutputSpan_eq_top supercuspidalMatrixSmoothing supercuspidalMatrixSmoothing_apply supercuspidalMatrixSmoothing_fourier_right supercuspidalMatrixSmoothing_fourier_singular supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalMatrixSmoothing_right supercuspidalMatrixSmoothing_singular transferBorel transferDisconnected transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferT2 transferTopology transferValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance extensionT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance extensionDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance extensionMeasurable : MeasurableSpace F := borel _
local instance extensionBorel : BorelSpace F := ⟨rfl⟩
local instance extensionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance extensionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hsd : IsSelfDual ψ ν)

/-- Restriction of bilinear matrix-test/vector pairings to the actual
Fourier-regular test submodule. -/
def fourierRegularMatrixPairingRestriction :
    (SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W) →ₗ[ℂ]
    (fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] V →ₗ[ℂ] W) where
  toFun B := B.comp (fourierRegularMatrixTests (m + 1) ψ ν hsd).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem fourierRegularMatrixPairingRestriction_apply
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
    fourierRegularMatrixPairingRestriction F ψ ν hsd B Φ w = B Φ.val w := rfl

variable (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
  (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible) (hm : 0 < m)
  (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F).toMonoidHom))

include hρ hi hm hι in
/-- A translation-compatible bilinear pairing vanishing on Fourier-regular
tests vanishes on every full-matrix test and every vector. -/
theorem matrixPairing_eq_zero_of_fourierRegular
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F),
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (hz : fourierRegularMatrixPairingRestriction F ψ ν hsd B = 0) :
    B = 0 := by
  apply LinearMap.ext
  intro Φ
  apply LinearMap.ext
  intro w
  have hle : supercuspidalCutoffOutputSpan F ρ hρ ≤ (B Φ).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ℓ, hℓ, v, x, rfl⟩
    change B Φ (Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
      (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) x) = 0
    rw [← supercuspidalConjugateMatrixSmoothing_pairing F ρ hρ ℓ hℓ B hB]
    let Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd :=
      ⟨supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v,
        supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests
          F ρ hρ ℓ hℓ hm hι ψ ν hsd Φ v⟩
    exact congrArg (fun T => T Ψ x) hz
  have hw : w ∈ supercuspidalCutoffOutputSpan F ρ hρ := by
    rw [supercuspidalCutoffOutputSpan_eq_top F ρ hρ hi]
    trivial
  exact hle hw

include hρ hi hm hι in
/-- Equality of two norm-one translation-compatible pairings is determined by
their restrictions to Fourier-regular matrix tests. -/
theorem matrixPairing_eq_of_fourierRegular
    (B D : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F),
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (hD : ∀ (g : GeneralLinear (m + 1) F),
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1 →
      ∀ Φ w, D (rectangularTranslate g Φ) w = D Φ (ρ g⁻¹ w))
    (heq : fourierRegularMatrixPairingRestriction F ψ ν hsd B =
      fourierRegularMatrixPairingRestriction F ψ ν hsd D) :
    B = D := by
  apply sub_eq_zero.mp
  apply matrixPairing_eq_zero_of_fourierRegular F ψ ν hsd ρ hρ hi hm hι (B - D)
  · intro g hg Φ w
    simp only [LinearMap.sub_apply, hB g hg, hD g hg]
  · rw [map_sub, heq, sub_self]

end Langlands.AllField.GodementJacquet.Padic
