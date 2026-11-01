import Langlands.Representation.GodementJacquet.ContinuedMatrixPairing
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate

/-! # Norm-one covariance of continued matrix pairings -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg
open RankinSelberg.RationalContinuationLinear
open scoped NNReal

universe uF uV

section General

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  (abv : AbsoluteValue F ℝ)
  (μ : Measure (Langlands.GeneralLinear (n + 1) F)) [μ.IsMulRightInvariant]

/-- Right translation of the full-matrix test transfers to inverse right
translation of the coefficient whenever the determinant has norm one. -/
theorem matrixIntegral_translate_of_norm_one
    (g : Langlands.GeneralLinear (n + 1) F) (hg : abv g.val.det = 1)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    matrixIntegral abv μ (rectangularTranslate g Φ) s f =
      matrixIntegral abv μ Φ s (fun h => f (h * g⁻¹)) := by
  have hw (h : Langlands.GeneralLinear (n + 1) F) :
      determinantWeight abv (h * g) s = determinantWeight abv h s := by
    simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul, hg, mul_one]
  unfold matrixIntegral
  calc
    _ = ∫ h, matrixIntegrand abv Φ s (fun k => f (k * g⁻¹)) (h * g) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with h
      simp only [matrixIntegrand, rectangularTranslate_apply, Units.val_mul,
        mul_inv_cancel_right, hw]
    _ = _ := integral_mul_right_eq_self _ g

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (q : ℕ)
  (C : V →ₗ[ℂ] (Langlands.GeneralLinear (n + 1) F → ℂ))
  (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
    ∃ R, HasShiftedRationalValue q abv μ Φ (C v) R)
  (hq : 1 < q)

/-- The unique actual rational pairing inherits norm-one translation covariance
from an explicit equality of coefficient functions. -/
theorem matrixRationalPairing_translate_of_norm_one
    (g : Langlands.GeneralLinear (n + 1) F) (hg : abv g.val.det = 1)
    (Φ : MatrixTestFunction n F) (v w : V)
    (hC : C w = fun h => C v (h * g⁻¹)) :
    matrixRationalPairing q abv μ C hRat hq (rectangularTranslate g Φ) v =
      matrixRationalPairing q abv μ C hRat hq Φ w := by
  apply (matrixRationalPairing_spec q abv μ C hRat hq
    (rectangularTranslate g Φ) v).2.unique hq
  apply continuation_of_eq_on_right
    (matrixRationalPairing_spec q abv μ C hRat hq Φ w).2
  refine ⟨0, fun s _ => ?_⟩
  rw [matrixIntegral_translate_of_norm_one abv μ g hg, ← hC]

end General

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance continuedMatrixCovarianceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance continuedMatrixCovarianceValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance continuedMatrixCovarianceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance continuedMatrixCovarianceT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance continuedMatrixCovarianceDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance continuedMatrixCovarianceMeasurable : MeasurableSpace F.Carrier := borel _
local instance continuedMatrixCovarianceBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance continuedMatrixCovarianceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance continuedMatrixCovarianceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abvF" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "μF" => generalLinearHaar F.Carrier n

/-- The original actual shifted rational matrix integral, bilinear in the
full-matrix test and the representation vector, for a fixed functional. -/
def matrixCoefficientRationalPairing
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R) :
    MatrixTestFunction n F.Carrier →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  matrixRationalPairing qF abvF μF (matrixCoefficient ρ ℓ) hRat
    F.canonicalTopologicalData.residueCardinality_gt_one

theorem matrixCoefficientRationalPairing_spec
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v)
      (matrixCoefficientRationalPairing F ρ ℓ hRat Φ v) :=
  matrixRationalPairing_spec qF abvF μF (matrixCoefficient ρ ℓ) hRat
    F.canonicalTopologicalData.residueCardinality_gt_one Φ v

/-- The original rational pairing has the covariance used in compact smoothing
transfer, with the inverse action on the vector. -/
theorem matrixCoefficientRationalPairing_translate
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    matrixCoefficientRationalPairing F ρ ℓ hRat (rectangularTranslate g Φ) v =
      matrixCoefficientRationalPairing F ρ ℓ hRat Φ (ρ g⁻¹ v) := by
  have hg' : abvF g.val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hg
  apply matrixRationalPairing_translate_of_norm_one abvF μF qF
    (matrixCoefficient ρ ℓ) hRat F.canonicalTopologicalData.residueCardinality_gt_one
    g hg' Φ v (ρ g⁻¹ v)
  funext h
  simp only [matrixCoefficient_apply, map_mul, Module.End.mul_apply]

/-- The actual full Fourier equivalence commutes with norm-one right
translation after replacing the translating matrix by its inverse transpose. -/
theorem matrixFourierEquiv_translate_of_norm_one
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F.Carrier) :
    rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd (rectangularTranslate g Φ) =
      rectangularTranslate (GeneralLinear.inverseTranspose (n + 1) F.Carrier g)
        (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ) := by
  apply Hecke.TestFunction.ext
  intro X
  rw [rectangularFourierEquiv_apply, rectangularTranslate_apply,
    rectangularFourierEquiv_apply]
  change rectangularFourierIntegral ψ ν (fun x => Φ (x * g.val)) X = _
  simpa only [Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_comp_mul_mul F.canonicalTopologicalData ψ ν
      1 g (map_one _) hg Φ X

/-- The actual inverse-transpose coefficient pairing after the full plus
Fourier transform, before reflection in the rational spectral variable. -/
def iotaFourierMatrixCoefficientRationalPairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R) :
    MatrixTestFunction n F.Carrier →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  (matrixRationalPairing qF abvF μF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    F.canonicalTopologicalData.residueCardinality_gt_one).comp
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd).toLinearMap

theorem iotaFourierMatrixCoefficientRationalPairing_spec
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ)
      (coefficientIota (matrixCoefficient ρ ℓ v))
      (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v) :=
  matrixRationalPairing_spec qF abvF μF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    F.canonicalTopologicalData.residueCardinality_gt_one _ v

/-- The Fourier and inverse-transpose operations cancel their changes to the
right action, giving the same covariance as the original rational pairing. -/
theorem iotaFourierMatrixCoefficientRationalPairing_translate
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        (rectangularTranslate g Φ) v =
      iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        Φ (ρ g⁻¹ v) := by
  have hg' : abvF g.val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hg
  have hιg : abvF (GeneralLinear.inverseTranspose (n + 1) F.Carrier g).val.det = 1 := by
    rw [GeneralLinear.inverseTranspose_coe, Matrix.det_transpose]
    change abvF ((Matrix.GeneralLinearGroup.det g⁻¹ : F.Carrierˣ) : F.Carrier) = 1
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    change (abvF g.val.det)⁻¹ = 1
    rw [hg', inv_one]
  change matrixRationalPairing qF abvF μF
      (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
      F.canonicalTopologicalData.residueCardinality_gt_one
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd (rectangularTranslate g Φ)) v = _
  rw [matrixFourierEquiv_translate_of_norm_one F ψ ν hsd g hg]
  apply matrixRationalPairing_translate_of_norm_one abvF μF qF
    (coefficientIotaLinearMap.comp (matrixCoefficient ρ ℓ)) hRat
    F.canonicalTopologicalData.residueCardinality_gt_one
    (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) hιg _ v (ρ g⁻¹ v)
  funext h
  change ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier h) (ρ g⁻¹ v)) =
    ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier
      (h * (GeneralLinear.inverseTranspose (n + 1) F.Carrier g)⁻¹)) v)
  simp only [map_mul, map_inv, GeneralLinear.inverseTranspose_involutive,
    Module.End.mul_apply]

end Padic

end Langlands.GodementJacquet
