import Langlands.Representation.GodementJacquet.MonomialMatrixCoefficientSpan
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixPairingExtension
import Langlands.Representation.GodementJacquet.FourierRegularRationalEquation

/-! # The rational supercuspidal equation for arbitrary matrix tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg LocalFactor GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rationalExtensionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance rationalExtensionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance rationalExtensionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance rationalExtensionT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance rationalExtensionDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance rationalExtensionMeasurable : MeasurableSpace F.Carrier := borel _
local instance rationalExtensionBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance rationalExtensionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance rationalExtensionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abvF" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "μF" => generalLinearHaar F.Carrier n

/-- The actual chosen Fourier and inverse-transpose rational pairing after
the normalized spectral reflection `X ↦ q⁻¹/X`. -/
def reflectedIotaFourierMatrixCoefficientRationalPairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R) :
    MatrixTestFunction n F.Carrier →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat).compr₂
    (RationalReflection.subst
      (spectralReflectionUnit (Nat.zero_lt_one.trans
        F.canonicalTopologicalData.residueCardinality_gt_one))).toLinearMap

@[simp]
theorem reflectedIotaFourierMatrixCoefficientRationalPairing_apply
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v =
      RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          F.canonicalTopologicalData.residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v) := rfl

/-- Rational spectral reflection preserves the norm-one translation rule. -/
theorem reflectedIotaFourierMatrixCoefficientRationalPairing_translate
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (g : GeneralLinear (n + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        (rectangularTranslate g Φ) v =
      reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        Φ (ρ g⁻¹ v) := by
  simp only [reflectedIotaFourierMatrixCoefficientRationalPairing_apply,
    iotaFourierMatrixCoefficientRationalPairing_translate F ψ ν hsd ρ ℓ hRat g hg]

/-- The global Fourier-regular operator equation extends to the actual
reflected rational pairings for every full-matrix test. -/
theorem matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator
    (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (hFE : ∀ (s : ℂ) (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ hι.1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) :
    RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          F.canonicalTopologicalData.residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat Φ v) =
      laurentToRatFunc (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k :
        LaurentCoefficients) * matrixCoefficientRationalPairing F ρ ℓ hRat Φ v := by
  let B := reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat
  let M := laurentToRatFunc
    (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k : LaurentCoefficients)
  let D := (matrixCoefficientRationalPairing F ρ ℓ hRat).compr₂
    (LinearMap.mulLeft ℂ M)
  have heq : B = D := by
    apply matrixPairing_eq_of_fourierRegular F ψ ν hsd ρ hρ hi hn hι B D
    · exact reflectedIotaFourierMatrixCoefficientRationalPairing_translate
        F ψ ν hsd ρ ℓ hIotaRat
    · intro g hg Ψ w
      change M * matrixCoefficientRationalPairing F ρ ℓ hRat
        (rectangularTranslate g Ψ) w =
          M * matrixCoefficientRationalPairing F ρ ℓ hRat Ψ (ρ g⁻¹ w)
      rw [matrixCoefficientRationalPairing_translate F ρ ℓ hRat g hg]
    · apply LinearMap.ext
      intro Ψ
      apply LinearMap.ext
      intro w
      exact matrixRationalPairing_identity_of_fourierRegular_operator
        F ρ hρ.1.1 hι.1.1 ψ ν hsd c k ℓ hRat hIotaRat Ψ (fun s => hFE s Ψ) w
  exact congrArg (fun T => T Φ v) heq

/-- For arbitrary full-matrix tests and a fixed coefficient functional, the
same shifted monomial gives the normalized equation for all supplied actual
original and Fourier-dual rational values. -/
theorem normalizedFunctionalEquation_of_supercuspidal_fourierRegular_operator
    (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (hFE : ∀ (s : ℂ) (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ hι.1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (Φ : MatrixTestFunction n F.Carrier) (v : V) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hD : HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ)
      (coefficientIota (matrixCoefficient ρ ℓ v)) RDual) :
    NormalizedFunctionalEquation qF 1 1 1
      (shiftedMatrixMonomialUnit F n c k) 0 k R RDual := by
  have hid := matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator
    F hn ρ hρ hi hι ψ ν hsd c k ℓ hRat hIotaRat hFE Φ v
  have hBR := (matrixCoefficientRationalPairing_spec F ρ ℓ hRat Φ v).2.unique
    F.canonicalTopologicalData.residueCardinality_gt_one hR.2
  have hDR := (iotaFourierMatrixCoefficientRationalPairing_spec
    F ψ ν hsd ρ ℓ hIotaRat Φ v).2.unique
      F.canonicalTopologicalData.residueCardinality_gt_one hD.2
  rw [hBR, hDR] at hid
  exact Langlands.GodementJacquet.normalizedFunctionalEquation_of_monomial_rational_identity
    F.canonicalTopologicalData.residueCardinality_gt_one hid

end Langlands.GodementJacquet.Padic
