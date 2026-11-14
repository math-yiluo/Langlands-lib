import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSmoothing
/-! # Conjugate coefficient smoothing and bilinear transfer -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel compactMatrixSmoothing_pairing conjugateSupercuspidalCutoffGroupTest conjugateSupercuspidalCutoffGroupTest_apply conjugateSupercuspidalCutoffGroupTest_eq_zero determinantWeight_locallyConstant determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_smoothFunctional_ne_zero generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation smoothingBorel smoothingDisconnected smoothingGLBorel smoothingGLMeasurable smoothingLocalField smoothingMeasurable smoothingT2 smoothingTopology smoothingValuativeRel supercuspidalConjugateMatrixSmoothing supercuspidalConjugateMatrixSmoothing_eq_integratedAction supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalConjugateMatrixSmoothing_pairing supercuspidalCutoffGroupTest supercuspidalCutoffGroupTest_apply supercuspidalMatrixSmoothing supercuspidalMatrixSmoothing_apply supercuspidalMatrixSmoothing_fourier_right supercuspidalMatrixSmoothing_fourier_singular supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalMatrixSmoothing_right supercuspidalMatrixSmoothing_singular transferBorel transferDisconnected transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferT2 transferTopology transferValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
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

local instance transferT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance transferDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance transferMeasurable : MeasurableSpace F := borel _
local instance transferBorel : BorelSpace F := ⟨rfl⟩
local instance transferGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance transferGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {m : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
  (hρ : IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

/-- The complex conjugate of the actual compact coefficient cutoff on GL. -/
def conjugateSupercuspidalCutoffGroupTest (v : V) :
    SchwartzBruhat (GeneralLinear (m + 1) F) :=
  ⟨fun g => starRingEnd ℂ (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g),
    (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v).locallyConstant.comp (starRingEnd ℂ),
    (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v).hasCompactSupport.comp_left
      (map_zero (starRingEnd ℂ))⟩

@[simp]
theorem conjugateSupercuspidalCutoffGroupTest_apply (v : V)
    (g : GeneralLinear (m + 1) F) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g =
      starRingEnd ℂ (supercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g) := rfl

theorem conjugateSupercuspidalCutoffGroupTest_eq_zero (v : V)
    (g : GeneralLinear (m + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g ≠ 1) :
    conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v g = 0 := by
  simp only [conjugateSupercuspidalCutoffGroupTest_apply,
    supercuspidalCutoffGroupTest_apply,
    supercuspidalCutoffMatrixTest_apply_of_not_mem (⟨⟩ : LocalFieldData F)
      (Nat.succ_pos m) ρ hρ ℓ hℓ v g hg, map_zero]

/-- Smoothing by the conjugate coefficient, defined through pointwise
conjugation of the proved supercuspidal smoothing. -/
def supercuspidalConjugateMatrixSmoothing
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
  conjugateMatrixTest (m + 1)
    (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ
      (conjugateMatrixTest (m + 1) Φ) v)

/-- This is the actual integrated action of the inverted conjugate cutoff. -/
theorem supercuspidalConjugateMatrixSmoothing_eq_integratedAction
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) :
    supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v =
      Hecke.integratedAction (generalLinearHaar F m)
        (rectangularSchwartzRepresentation (K := F)
          (r := m + 1) (s := m + 1))
        rectangularSchwartzRepresentation_isSmooth
        (Hecke.TestFunction.inversion
          (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v)) Φ := by
  ext X
  let ev : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => Ψ X, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change starRingEnd ℂ (ev
    (supercuspidalMatrixSmoothing F ρ hρ ℓ hℓ
      (conjugateMatrixTest (m + 1) Φ) v)) = ev _
  rw [supercuspidalMatrixSmoothing_apply, Hecke.integratedAction_dual,
    Hecke.integratedAction_dual, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [Hecke.TestFunction.inversion_apply,
    conjugateSupercuspidalCutoffGroupTest_apply, ev,
    LinearMap.coe_mk, AddHom.coe_mk,
    rectangularSchwartzRepresentation_apply, rectangularTranslate_apply,
    conjugateMatrixTest_apply, map_mul, starRingEnd_self_apply]

/-- Conjugated smoothing retains both singular-vanishing conditions. -/
theorem supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests
    (hm : 0 < m)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (m + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v : V) :
    supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v ∈
      fourierRegularMatrixTests (m + 1) ψ ν hsd :=
  conjugate_mem_fourierRegularMatrixTests (m + 1) ψ ν hsd
    (supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests
      F ρ hρ ℓ hℓ hm hι ψ ν hsd (conjugateMatrixTest (m + 1) Φ) v)

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A translation-compatible bilinear pairing commutes with compact smoothing
on determinant norm one. The proof uses only finite-fiber integration. -/
theorem compactMatrixSmoothing_pairing
    (hsm : IsSmooth ρ)
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F),
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (f : SchwartzBruhat (GeneralLinear (m + 1) F))
    (hf : ∀ g, (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g ≠ 1 → f g = 0)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (w : V) :
    B (Hecke.integratedAction (generalLinearHaar F m)
      (rectangularSchwartzRepresentation (K := F) (r := m + 1) (s := m + 1))
      rectangularSchwartzRepresentation_isSmooth (Hecke.TestFunction.inversion f) Φ) w =
      B Φ (Hecke.integratedAction (generalLinearHaar F m) ρ hsm f w) := by
  let τ := rectangularSchwartzRepresentation
    (K := F) (r := m + 1) (s := m + 1)
  let hτ : IsSmooth τ := rectangularSchwartzRepresentation_isSmooth
  let μ := generalLinearHaar F m
  let : Measure.IsInvInvariant μ := (generalLinearHaarSymmetries F m).1
  change (B.flip w) (AlgebraicIntegral.integral μ
      (Hecke.actionIntegrand τ hτ (Hecke.TestFunction.inversion f) Φ)) =
    B Φ (AlgebraicIntegral.integral μ (Hecke.actionIntegrand ρ hsm f w))
  rw [← AlgebraicIntegral.integral_linearMap _
      (Hecke.actionIntegrand_finMeasSupp μ τ hτ (Hecke.TestFunction.inversion f) Φ),
    ← AlgebraicIntegral.integral_linearMap _
      (Hecke.actionIntegrand_finMeasSupp μ ρ hsm f w)]
  rw [← AlgebraicIntegral.integral_comp_measurePreserving
    ((Hecke.actionIntegrand τ hτ (Hecke.TestFunction.inversion f) Φ).map (B.flip w))
    Inv.inv (Measure.measurePreserving_inv μ)]
  congr 1
  ext g
  change B ((Hecke.TestFunction.inversion f) g⁻¹ • τ g⁻¹ Φ) w =
    B Φ (f g • ρ g w)
  simp only [Hecke.TestFunction.inversion_apply, inv_inv, map_smul, LinearMap.smul_apply]
  by_cases hg : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1
  · have hgi : (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g⁻¹ = 1 := by
      rw [map_inv, hg, inv_one]
    simpa only [τ, rectangularSchwartzRepresentation_apply,
      inv_inv] using congrArg (fun z => f g • z) (hB g⁻¹ hgi Φ w)
  · simp [hf g hg]

/-- Both continued zeta pairings can use this same integrated rho output. -/
theorem supercuspidalConjugateMatrixSmoothing_pairing
    (B : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F) →ₗ[ℂ]
      V →ₗ[ℂ] W)
    (hB : ∀ (g : GeneralLinear (m + 1) F),
      (⟨⟩ : LocalFieldData F).determinantNorm (m + 1) g = 1 →
      ∀ Φ w, B (rectangularTranslate g Φ) w = B Φ (ρ g⁻¹ w))
    (Φ : SchwartzBruhat (Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (v w : V) :
    B (supercuspidalConjugateMatrixSmoothing F ρ hρ ℓ hℓ Φ v) w =
      B Φ (Hecke.integratedAction (generalLinearHaar F m) ρ hρ.1.1
        (conjugateSupercuspidalCutoffGroupTest F ρ hρ ℓ hℓ v) w) := by
  rw [supercuspidalConjugateMatrixSmoothing_eq_integratedAction]
  exact compactMatrixSmoothing_pairing F ρ hρ.1.1 B hB _
    (conjugateSupercuspidalCutoffGroupTest_eq_zero F ρ hρ ℓ hℓ v) Φ w

end Langlands.AllField.GodementJacquet.Padic
