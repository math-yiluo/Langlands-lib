import Langlands.Representation.GodementJacquet.FourierRegularMatrixTranslates
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! # Invertible translations of Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped NNReal

universe uF

section General


end General

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 leftRightTranslate_mem_fourierRegularMatrixTests matrixIntegral matrixIntegrand matrixRationalValues translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance translatesT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance translatesDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance translatesMeasurable : MeasurableSpace F := borel _
local instance translatesBorel : BorelSpace F := ⟨rfl⟩

variable {d : ℕ}

/-- Arbitrary invertible translates preserve both actual singular-vanishing
conditions. The Fourier change of variables retains its Haar-scaling factor. -/
theorem leftRightTranslate_mem_fourierRegularMatrixTests
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F)
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) F)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    rectangularLeftRightTranslate A B Φ ∈ fourierRegularMatrixTests d ψ ν hsd := by
  refine ⟨leftRightTranslate_mem_regularMatrixTests A B hΦ.1, ?_⟩
  intro X hX
  change rectangularFourierEquiv ψ ν d d hsd
    (rectangularLeftRightTranslate A B Φ) X = 0
  rw [rectangularFourierEquiv_apply]
  let T := (⟨⟩ : LocalFieldData F)
  let := T.secondCountableTopology
  let c : ℝ≥0 :=
    (((T.determinantNorm d A : ℝ≥0) ^ d /
      (T.determinantNorm d B⁻¹ : ℝ≥0) ^ d)⁻¹)
  have hm : (RankinSelberg.rectangularMeasure ν d d).map
      (rectangularLeftRightHomeomorph A B) =
      c • RankinSelberg.rectangularMeasure ν d d := by
    change (RankinSelberg.rectangularMeasure ν d d).map
      (fun X => A.val * X * B.val) = c • RankinSelberg.rectangularMeasure ν d d
    simpa only [inv_inv] using padicRectangularHaarScaling F T d d
      (RankinSelberg.rectangularMeasure ν d d) A B⁻¹
  change rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X = 0
  rw [rectangularFourierIntegral_leftRight ψ ν A B c hm]
  have hz := hΦ.2
    ((GeneralLinear.inverseTranspose d F A).val * X *
      (GeneralLinear.inverseTranspose d F B).val)
    (by
      intro h
      apply hX
      simpa only [Units.isUnit_mul_units, Units.isUnit_units_mul] using h)
  change rectangularFourierEquiv ψ ν d d hsd Φ _ = 0 at hz
  rw [rectangularFourierEquiv_apply] at hz
  rw [hz, mul_zero]

/-- Actual invertible left-right translation on Fourier-regular tests. -/
def fourierRegularMatrixTranslate
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F) :
    fourierRegularMatrixTests d ψ ν hsd →ₗ[ℂ]
      fourierRegularMatrixTests d ψ ν hsd where
  toFun Φ := ⟨rectangularLeftRightTranslate A B Φ.val,
    leftRightTranslate_mem_fourierRegularMatrixTests F ψ ν hsd A B Φ.property⟩
  map_add' Φ Ψ := Subtype.ext ((rectangularLeftRightTranslate A B).map_add Φ.val Ψ.val)
  map_smul' c Φ := Subtype.ext ((rectangularLeftRightTranslate A B).map_smul c Φ.val)

@[simp] theorem fourierRegularMatrixTranslate_apply
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F)
    (Φ : fourierRegularMatrixTests d ψ ν hsd)
    (X : Matrix (Fin d) (Fin d) F) :
    (fourierRegularMatrixTranslate F ψ ν hsd A B Φ).val X =
      Φ.val (A.val * X * B.val) := rfl

end Padic

end Langlands.AllField.GodementJacquet
