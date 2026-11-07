import Langlands.Representation.GodementJacquet.TateCharacterNormalizer
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Representation.RankinSelberg.PadicPairLFactor

/-! Exact abelian Euler polynomials for actual rank-one matrix and JPSS values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : MeasurableSpace F.Carrierˣ := borel _
local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
  (χ : Quasicharacter F.Carrier)

/-- Exact normalization transfers through equality of the actual value families. -/
theorem tateCharacter_matrixNormalizedGenerator [Nontrivial V]
    (hσ : IsSmooth σ) (hact : TateCharacterAction σ χ) :
    IsMatrixNormalizedGenerator F σ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ) := by
  change IsNormalizedGenerator (matrixRationalValues F σ) _
  rw [tateMatrixRationalValues_eq_scalar F σ χ hσ hact]
  exact scalarMellin_character_isNormalizedGenerator F F.canonicalTopologicalData χ

/-- Inverse transpose gives precisely the inverse-character Euler polynomial. -/
theorem tateCharacter_iotaMatrixNormalizedGenerator [Nontrivial V]
    (hσ : IsSmooth σ) (hact : TateCharacterAction σ χ) :
    IsIotaMatrixNormalizedGenerator F σ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ⁻¹) := by
  change IsNormalizedGenerator (iotaMatrixRationalValues F σ) _
  rw [tateIotaMatrixRationalValues_eq_scalar F σ χ hσ hact]
  exact scalarMellin_character_isNormalizedGenerator F F.canonicalTopologicalData χ⁻¹

/-- The ordinary analytic predicate has the specified abelian polynomial. -/
theorem tateCharacter_matrixAnalyticAssertions [Nontrivial V]
    (hσ : IsSmooth σ) (hact : TateCharacterAction σ χ) :
    MatrixAnalyticAssertions F σ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ) := by
  obtain ⟨P, hc, hr, -⟩ := exists_tateMatrixAnalyticAssertions F σ χ hσ hact
  exact ⟨hc, hr, tateCharacter_matrixNormalizedGenerator F σ χ hσ hact⟩

/-- The transformed analytic predicate has the inverse-character polynomial. -/
theorem tateCharacter_iotaMatrixAnalyticAssertions [Nontrivial V]
    (hσ : IsSmooth σ) (hact : TateCharacterAction σ χ) :
    IotaMatrixAnalyticAssertions F σ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ⁻¹) := by
  obtain ⟨P, hc, hr, -⟩ := exists_tateIotaMatrixAnalyticAssertions F σ χ hσ hact
  exact ⟨hc, hr, tateCharacter_iotaMatrixNormalizedGenerator F σ χ hσ hact⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier)

local instance (ℓ : glFunctionals ψ 0 σ) :
    AddCommGroup (glCoefficientModel ψ 0 σ ℓ).toSubmodule :=
  (glCoefficientModel ψ 0 σ ℓ).toSubmodule.addCommGroup

/-- Scalar action descends through the canonical surjection onto the model. -/
theorem tateCharacter_model_action (hact : TateCharacterAction σ χ)
    (ℓ : glFunctionals ψ 0 σ) :
    TateCharacterAction (glModelRepresentation ψ 0 σ ℓ) χ := by
  intro g w
  obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ w
  rw [← (modelMap σ ℓ).isIntertwining, hact, map_smul]

/-- The actual standard JPSS polynomial is the abelian Euler polynomial. -/
theorem tateCharacter_isCharacterLPolynomial
    (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
    (hact : TateCharacterAction σ χ)
    (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
    (hμ : IsCompatible (upperUnipotent 1 F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ) :
    IsCharacterLPolynomial F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ 1 σ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ) := by
  obtain ⟨e⟩ := hσ.2.2
  let ℓ : glFunctionals ψ 0 σ := e.symm 1
  have hℓ : ℓ.val ≠ 0 := by
    intro h
    have hz : ℓ = 0 := Subtype.ext h
    have he := congrArg e hz
    simp [ℓ] at he
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  have hmv : modelMap σ ℓ v ≠ 0 := by
    intro h
    apply hv
    have h1 : ((modelMap σ ℓ v).val).val 1 = 0 := by rw [h]; rfl
    change ℓ.val (σ 1 v) = 0 at h1
    simpa using h1
  let : Nontrivial (glCoefficientModel ψ 0 σ ℓ).toSubmodule :=
    ⟨⟨modelMap σ ℓ v, 0, hmv⟩⟩
  have hgen := tateCharacter_matrixNormalizedGenerator F
    (glModelRepresentation ψ 0 σ ℓ) χ (glModel_isSmooth ψ 0 σ hσ.1.1 ℓ)
    (tateCharacter_model_action F σ χ ψ hact ℓ)
  have h13 := rankOneMatrixWhittakerComparison p F ψ 0 V σ hσ ℓ hℓ μ hμ
  have h23 := GodementJacquet.whittakerModelComparison p F ψ 0 σ hσ ℓ hℓ
  exact (isNormalizedGenerator_congr (h13.trans h23.symm) _).mpr hgen

/-- A pair of actual character representations has the product-character
abelian polynomial, for every supplied additive Haar measure. -/
theorem rankOneCharacters_isPadicPairLPolynomial
    (η : Quasicharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier) :
    IsPadicPairLPolynomial F ψ ν
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
      (rankOneCharacter (η : F.Carrierˣ →* ℂˣ))
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)) := by
  constructor
  · exact ⟨inferInstance, unipotent_compatibleMeasureExists F.Carrier 0⟩
  · intro _ μ hμ
    have htwist : Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant)
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) =
        rankOneCharacter ((χ * η : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ) := by
      ext g
      simp [rankOneCharacter, characterRepresentation, twist, mul_comm]
    have hstandard := tateCharacter_isCharacterLPolynomial F
      (rankOneCharacter ((χ * η : Quasicharacter F.Carrier) : F.Carrierˣ →* ℂˣ))
      (χ * η) ψ (rankOneCharacter_isOfWhittakerType p F ψ (χ * η))
      (by intro g v; rfl) μ hμ
    rw [← htwist] at hstandard
    exact isPairLPolynomial_self.mpr
      ((isStandardLPolynomial_twist F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (η : F.Carrierˣ →* ℂˣ) (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)) _).mp hstandard)

/-- The all-character rank-one JPSS L-polynomial assertion, with the actual
product-character abelian Euler polynomial and every additive Haar measure. -/
def RankOneCharactersLPolynomialStatement : Prop :=
  ∀ (χ η : Quasicharacter F.Carrier) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier),
    IsPadicPairLPolynomial F ψ ν
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
      (rankOneCharacter (η : F.Carrierˣ →* ℂˣ))
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η))

theorem rankOneCharactersLPolynomialStatement :
    RankOneCharactersLPolynomialStatement F := by
  intro χ η ψ ν
  exact rankOneCharacters_isPadicPairLPolynomial F χ ψ η ν

end Langlands.GodementJacquet.Padic
