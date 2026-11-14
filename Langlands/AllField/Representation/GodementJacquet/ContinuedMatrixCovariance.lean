import Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance
import Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-! # Norm-one covariance of continued matrix pairings -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicRectangularHaarScaling padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg.RationalContinuationLinear
open scoped NNReal

universe uF uV

section General



end General

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData continuedMatrixCovarianceBorel continuedMatrixCovarianceDisconnected continuedMatrixCovarianceGLBorel continuedMatrixCovarianceGLMeasurable continuedMatrixCovarianceLocalField continuedMatrixCovarianceMeasurable continuedMatrixCovarianceT2 continuedMatrixCovarianceTopology continuedMatrixCovarianceValuation instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaFourierMatrixCoefficientRationalPairing iotaFourierMatrixCoefficientRationalPairing_spec iotaFourierMatrixCoefficientRationalPairing_translate iotaMatrixRationalValues jpssI2 jpssI3 matrixCoefficientRationalPairing matrixCoefficientRationalPairing_spec matrixCoefficientRationalPairing_translate matrixFourierEquiv_translate_of_norm_one matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance continuedMatrixCovarianceT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance continuedMatrixCovarianceDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance continuedMatrixCovarianceMeasurable : MeasurableSpace F := borel _
local instance continuedMatrixCovarianceBorel : BorelSpace F := ⟨rfl⟩
local instance continuedMatrixCovarianceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance continuedMatrixCovarianceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abvF" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "μF" => generalLinearHaar F n

/-- The original actual shifted rational matrix integral, bilinear in the
full-matrix test and the representation vector, for a fixed functional. -/
def matrixCoefficientRationalPairing
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R) :
    MatrixTestFunction n F →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  matrixRationalPairing qF abvF μF (matrixCoefficient ρ ℓ) hRat
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one

theorem matrixCoefficientRationalPairing_spec
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (Φ : MatrixTestFunction n F) (v : V) :
    HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v)
      (matrixCoefficientRationalPairing F ρ ℓ hRat Φ v) :=
  matrixRationalPairing_spec qF abvF μF (matrixCoefficient ρ ℓ) hRat
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one Φ v

/-- The original rational pairing has the covariance used in compact smoothing
transfer, with the inverse action on the vector. -/
theorem matrixCoefficientRationalPairing_translate
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F) (v : V) :
    matrixCoefficientRationalPairing F ρ ℓ hRat (rectangularTranslate g Φ) v =
      matrixCoefficientRationalPairing F ρ ℓ hRat Φ (ρ g⁻¹ v) := by
  have hg' : abvF g.val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hg
  apply matrixRationalPairing_translate_of_norm_one abvF μF qF
    (matrixCoefficient ρ ℓ) hRat (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    g hg' Φ v (ρ g⁻¹ v)
  funext h
  simp only [matrixCoefficient_apply, map_mul, Module.End.mul_apply]

/-- The actual full Fourier equivalence commutes with norm-one right
translation after replacing the translating matrix by its inverse transpose. -/
theorem matrixFourierEquiv_translate_of_norm_one
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F) :
    rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd (rectangularTranslate g Φ) =
      rectangularTranslate (GeneralLinear.inverseTranspose (n + 1) F g)
        (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ) := by
  apply Hecke.TestFunction.ext
  intro X
  rw [rectangularFourierEquiv_apply, rectangularTranslate_apply,
    rectangularFourierEquiv_apply]
  change rectangularFourierIntegral ψ ν (fun x => Φ (x * g.val)) X = _
  simpa only [Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_comp_mul_mul (⟨⟩ : LocalFieldData F) ψ ν
      1 g (map_one _) hg Φ X

/-- The actual inverse-transpose coefficient pairing after the full plus
Fourier transform, before reflection in the rational spectral variable. -/
def iotaFourierMatrixCoefficientRationalPairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R) :
    MatrixTestFunction n F →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  (matrixRationalPairing qF abvF μF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one).comp
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd).toLinearMap

theorem iotaFourierMatrixCoefficientRationalPairing_spec
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : MatrixTestFunction n F) (v : V) :
    HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ)
      (coefficientIota (matrixCoefficient ρ ℓ v))
      (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v) :=
  matrixRationalPairing_spec qF abvF μF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one _ v

/-- The Fourier and inverse-transpose operations cancel their changes to the
right action, giving the same covariance as the original rational pairing. -/
theorem iotaFourierMatrixCoefficientRationalPairing_translate
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F) (v : V) :
    iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        (rectangularTranslate g Φ) v =
      iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        Φ (ρ g⁻¹ v) := by
  have hg' : abvF g.val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hg
  have hιg : abvF (GeneralLinear.inverseTranspose (n + 1) F g).val.det = 1 := by
    rw [GeneralLinear.inverseTranspose_coe, Matrix.det_transpose]
    change abvF ((Matrix.GeneralLinearGroup.det g⁻¹ : Fˣ) : F) = 1
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    change (abvF g.val.det)⁻¹ = 1
    rw [hg', inv_one]
  change matrixRationalPairing qF abvF μF
      (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd (rectangularTranslate g Φ)) v = _
  rw [matrixFourierEquiv_translate_of_norm_one F ψ ν hsd g hg]
  apply matrixRationalPairing_translate_of_norm_one abvF μF qF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    (GeneralLinear.inverseTranspose (n + 1) F g) hιg _ v (ρ g⁻¹ v)
  funext h
  change ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F h) (ρ g⁻¹ v)) =
    ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F
      (h * (GeneralLinear.inverseTranspose (n + 1) F g)⁻¹)) v)
  simp only [map_mul, map_inv, GeneralLinear.inverseTranspose_involutive,
    Module.End.mul_apply]

end Padic

end Langlands.AllField.GodementJacquet
