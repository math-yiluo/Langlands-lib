import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonZeroPadic

/-! Scalar Tate functional equation from the independent equal-rank theorem. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear QuotientIntegration

universe uF

section Coordinates

variable (K : Type uF) [TopologicalSpace K]

/-- Evaluation of the unique row coordinate. -/
def tateRowScalarHomeomorph : (Fin 1 → K) ≃ₜ K :=
  Homeomorph.piUnique (fun _ : Fin 1 => K)

/-- A scalar test regarded as a one-coordinate row test. -/
def tateRowTest (Φ : SchwartzBruhat K) : SchwartzBruhat (Fin 1 → K) :=
  Hecke.TestFunction.pullback (tateRowScalarHomeomorph K) Φ

/-- A row test regarded as a scalar test. -/
def tateScalarRowTest (Φ : SchwartzBruhat (Fin 1 → K)) : SchwartzBruhat K :=
  Hecke.TestFunction.pullback (tateRowScalarHomeomorph K).symm Φ

@[simp] theorem tateRowTest_apply (Φ : SchwartzBruhat K) (x : Fin 1 → K) :
    tateRowTest K Φ x = Φ (x 0) := rfl

@[simp] theorem tateScalarRowTest_apply (Φ : SchwartzBruhat (Fin 1 → K)) (x : K) :
    tateScalarRowTest K Φ x = Φ (fun _ => x) := rfl

@[simp] theorem tateScalarRowTest_tateRowTest (Φ : SchwartzBruhat K) :
    tateScalarRowTest K (tateRowTest K Φ) = Φ := rfl

variable [Field K]

/-- The identity form on the actual scalar character model. -/
def tateCharacterFunctional (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ) :
    glFunctionals ψ 0 (rankOneCharacter χ) :=
  ⟨LinearMap.id, by rw [glFunctionals_rankOne]; trivial⟩

theorem tateCharacterFunctional_ne_zero
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ) :
    (tateCharacterFunctional K ψ χ).val ≠ 0 := by
  intro h
  have h1 := congrArg (fun L : Module.Dual ℂ ℂ => L 1) h
  exact one_ne_zero h1

/-- Every coefficient is its value at one times the character. -/
theorem tateCharacterModel_apply
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ)
    (f : (coefficientModel (rankOneCharacter χ)
      (tateCharacterFunctional K ψ χ)).toSubmodule)
    (g : Langlands.GeneralLinear 1 K) :
    f.val.val g = (χ (determinant g) : ℂ) * f.val.val 1 := by
  obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f
  change rankOneCharacter χ g z =
    (χ (determinant g) : ℂ) * rankOneCharacter χ 1 z
  simp [rankOneCharacter, characterRepresentation, twist]

end Coordinates

section Fourier

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]

omit [IsTopologicalRing K] [BorelSpace K] in
/-- The one-coordinate row Fourier integral is the supplied scalar integral. -/
theorem rowFourierIntegral_tateRowTest
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (Φ : SchwartzBruhat K) (y : Fin 1 → K) :
    rowFourierIntegral ψ ν 1 (tateRowTest K Φ) y =
      fourierIntegral ψ ν Φ (y 0) := by
  unfold rowFourierIntegral fourierIntegral
  simp only [tateRowTest_apply, rowPairing, Fin.sum_univ_one]
  exact (measurePreserving_piUnique (fun _ : Fin 1 => ν.measure)).integral_comp
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => K)).measurableEmbedding
    (fun x => ψ.complex (x * y 0) * Φ x)

/-- A row Fourier witness gives an integrable scalar Fourier witness. -/
theorem tateScalarFourierPair_of_row
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (Φ : SchwartzBruhat K) (Ψ : SchwartzBruhat (Fin 1 → K))
    (h : IsRowFourierPair ψ ν (tateRowTest K Φ) Ψ) :
    ∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
      tateScalarRowTest K Ψ y = fourierIntegral ψ ν Φ y := by
  intro y
  refine ⟨fourierIntegrand_integrable ψ ν Φ y, ?_⟩
  exact (h (fun _ => y)).trans (rowFourierIntegral_tateRowTest ψ ν Φ _)

end Fourier

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance tateFETopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance tateFEValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance tateFELocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance tateFET2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance tateFETotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance tateFEMeasurable : MeasurableSpace F.Carrier := borel _
local instance tateFEBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance tateFEUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance tateFEUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance tateFEGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance tateFEGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance tateFEUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance tateFEUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance tateFEQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance tateFEQuotientBorel : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "q" => F.canonicalTopologicalData.residueCardinality
local notation "μ" => localMultiplicativeHaar F.Carrier

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (χ : Quasicharacter F.Carrier)

local notation "πχ" => rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)
local notation "π₁" => rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ)
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ

/-- Original model integrals are scalar Mellin integrals, with the two vector
coordinates absorbed into the test. -/
theorem tateEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F.Carrier)) (s : ℂ) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F.Carrier)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
        (fun a => (χ a : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F.Carrier Φ) s := by
  unfold equalRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  have hdet : determinant (tateScalarEquiv F.Carrier a) = a :=
    (tateScalarEquiv F.Carrier).symm_apply_apply a
  have hdetval : (tateScalarEquiv F.Carrier a).val.det = (a : F.Carrier) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F.Carrier a) = fun _ => (a : F.Carrier) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction,
    tateCharacterModel_apply F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ) f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdet, hdetval, hrow]
  change (χ a : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F.Carrier)) *
    (F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℂ) ^ s = _
  ring

/-- The transformed model integrals use the inverse multiplicative character. -/
theorem tateDualEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F.Carrier)) (s : ℂ) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F.Carrier)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F.Carrier Φ) s := by
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  have hdet : determinant (tateScalarEquiv F.Carrier a) = a :=
    (tateScalarEquiv F.Carrier).symm_apply_apply a
  have hdetval : (tateScalarEquiv F.Carrier a).val.det = (a : F.Carrier) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F.Carrier a) = fun _ => (a : F.Carrier) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction, firstDualFunction_apply, secondDualFunction_apply,
    weylLong_rankOne_eq_one, one_mul,
    tateCharacterModel_apply F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ) f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _,
    RankOneGammaTwist.determinant_inverseTranspose, hdet]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdetval, hrow,
    map_inv, Units.val_inv_eq_inv_val]
  change ((χ a)⁻¹ : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F.Carrier)) *
    (F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℂ) ^ s = _
  ring

/-- The coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateCharacterModelOne_at_one :
    (modelMap πχ ℓχ (1 : ℂ)).val.val 1 = 1 := by
  change (πχ 1) (1 : ℂ) = 1
  simp

/-- The trivial coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateTrivialModelOne_at_one :
    (modelMap π₁ ℓ₁ (1 : ℂ)).val.val 1 = 1 := by
  change (π₁ 1) (1 : ℂ) = 1
  simp

/-- At unit model vectors, only the row-to-scalar test transport remains. -/
theorem tateEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F.Carrier)) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F.Carrier)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
        (fun a => (χ a : ℂ)) 1 (tateScalarRowTest F.Carrier Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateEqualRankIntegral_eq_scalar F ψ χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- The unit dual model vectors give exactly the inverse-character Mellin test. -/
theorem tateDualEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F.Carrier)) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F.Carrier)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 (tateScalarRowTest F.Carrier Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateDualEqualRankIntegral_eq_scalar F ψ χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- Equality of the complete original rational-value families. -/
theorem tateEqualRankRationalValues_eq_scalar :
    equalRankRationalValues q ψ abv (rankOneQuotientHaar F.Carrier) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q F.canonicalTopologicalData.normalizedAbs μ
        (fun a => (χ a : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F.Carrier Φ, ?_⟩
    have heq := funext (tateEqualRankIntegral_eq_scalar F ψ χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F.Carrier Φ, ?_⟩
    rwa [tateEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- Equality of the complete dual rational-value families. -/
theorem tateDualEqualRankRationalValues_eq_scalar :
    dualEqualRankRationalValues q ψ abv (rankOneQuotientHaar F.Carrier) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q F.canonicalTopologicalData.normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F.Carrier Φ, ?_⟩
    have heq := funext (tateDualEqualRankIntegral_eq_scalar F ψ χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F.Carrier Φ, ?_⟩
    rwa [tateDualEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- The scalar Tate functional equation for the exact supplied self-dual Haar
measure. The epsilon constant and exponent are chosen before every scalar test;
the equation holds for every pair of its actual rational continuations. -/
theorem tateScalarFunctionalEquation
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
    {P PDual : Polynomial ℂ}
    (hP : IsNormalizedGenerator
      (scalarMellinRationalValues q F.canonicalTopologicalData.normalizedAbs μ
        (fun a => (χ a : ℂ)) 1) P)
    (hPDual : IsNormalizedGenerator
      (scalarMellinRationalValues q F.canonicalTopologicalData.normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1) PDual) :
    ∃ (c : ℂˣ) (a : ℤ), ∀ Φ : SchwartzBruhat F.Carrier,
      ∃ Φhat : SchwartzBruhat F.Carrier,
        (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
          Φhat y = fourierIntegral ψ ν Φ y) ∧
        ∀ R RDual : RationalFunctions,
          HasRationalContinuation q
            (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
              (fun x => (χ x : ℂ)) 1 Φ) R →
          HasRationalContinuation q
            (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs μ
              (fun x => ((χ x)⁻¹ : ℂ)) 1 Φhat) RDual →
          NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual := by
  have hχ := rankOneCharacter_isOfWhittakerType p F ψ χ
  have h₁ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) π₁ := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    exact rankOneCharacter_isOfWhittakerType p F ψ 1
  let := unipotentHaar_isMulRightInvariant F.Carrier 0
  obtain ⟨ζ, c, a, Q, QDual, -, hQ, hQDual, hFE⟩ :=
    equalRankFunctionalEquation.{uF, 0, 0} F F.canonicalTopologicalData 0 ψ
      (rankOneQuotientHaar F.Carrier) (rankOneQuotientHaar_isCompatible F.Carrier)
      ν hν ℂ ℂ πχ π₁ hχ h₁ ℓχ ℓ₁
      (tateCharacterFunctional_ne_zero F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional_ne_zero ψ)
  rw [tateEqualRankRationalValues_eq_scalar] at hQ
  rw [tateDualEqualRankRationalValues_eq_scalar] at hQDual
  obtain rfl := IsNormalizedGenerator.unique hQ hP
  obtain rfl := IsNormalizedGenerator.unique hQDual hPDual
  refine ⟨c, a, fun Φ => ?_⟩
  obtain ⟨Ψ, R₀, RDual₀, hFourier, hR₀, hRDual₀, hNorm⟩ :=
    hFE (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) (tateRowTest F.Carrier Φ)
  rw [tateEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest] at hR₀
  rw [tateDualEqualRankIntegral_unit_eq_scalar] at hRDual₀
  refine ⟨tateScalarRowTest F.Carrier Ψ,
    tateScalarFourierPair_of_row ψ ν Φ Ψ hFourier, ?_⟩
  intro R RDual hR hRDual
  obtain rfl := hR.unique F.canonicalTopologicalData.residueCardinality_gt_one hR₀
  obtain rfl := hRDual.unique F.canonicalTopologicalData.residueCardinality_gt_one hRDual₀
  simpa only [NormalizedFunctionalEquation, pow_zero] using hNorm

end Padic

end Langlands.GodementJacquet
