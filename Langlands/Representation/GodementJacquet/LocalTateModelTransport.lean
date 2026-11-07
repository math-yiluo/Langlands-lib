import Langlands.Representation.GodementJacquet.LocalTateTransport

/-! Exact scalar transport of the rank-one JPSS coefficient integrals and value families. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear QuotientIntegration

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (χ : Fˣ →* ℂˣ) (q : ℕ)

local notation "πχ" => rankOneCharacter χ
local notation "π₁" => rankOneCharacter (1 : Fˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F ψ χ
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ
local notation "μ" => localMultiplicativeHaar F

/-- The actual scalar test absorbing both rank-one coefficient values. -/
def tateCoefficientTest
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) : SchwartzBruhat F :=
  (f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ

omit [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)] in
/-- The original coefficient integrand in scalar coordinates. -/
theorem tateEqualRankFunction_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) (a : Fˣ) :
    equalRankFunction ψ abv f.val f'.val Φ s (tateScalarEquiv F a) =
      scalarMellinIntegrand abv (fun a => (χ a : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s a := by
  have hdet : determinant (tateScalarEquiv F a) = a :=
    (tateScalarEquiv F).symm_apply_apply a
  have hdetval : (tateScalarEquiv F a).val.det = (a : F) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F a) = fun _ => (a : F) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction,
    tateCharacterModel_apply F ψ χ f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdet, hdetval, hrow]
  change (χ a : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F)) *
    (abv (a : F) : ℂ) ^ s = _
  ring


/-- Original model integrals are scalar Mellin integrals, with the two vector
coordinates absorbed into the test. -/
theorem tateEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral abv μ
        (fun a => (χ a : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s := by
  unfold equalRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  exact tateEqualRankFunction_eq_scalar F ψ abv χ f f' Φ s a

omit [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)] in
/-- The dual coefficient integrand in scalar coordinates. -/
theorem tateDualEqualRankFunction_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) (a : Fˣ) :
    equalRankFunction (ψ.scale (-1)) abv (firstDualFunction ψ 0 f.val)
        (secondDualFunction ψ 0 f'.val) Φ s (tateScalarEquiv F a) =
      scalarMellinIntegrand abv (fun a => ((χ a)⁻¹ : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s a := by
  have hdet : determinant (tateScalarEquiv F a) = a :=
    (tateScalarEquiv F).symm_apply_apply a
  have hdetval : (tateScalarEquiv F a).val.det = (a : F) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F a) = fun _ => (a : F) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction, firstDualFunction_apply, secondDualFunction_apply,
    weylLong_rankOne_eq_one, one_mul,
    tateCharacterModel_apply F ψ χ f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _,
    RankOneGammaTwist.determinant_inverseTranspose, hdet]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdetval, hrow,
    map_inv, Units.val_inv_eq_inv_val]
  change ((χ a)⁻¹ : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F)) *
    (abv (a : F) : ℂ) ^ s = _
  ring

/-- The transformed model integrals use the inverse multiplicative character. -/
theorem tateDualEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral abv μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s := by
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  exact tateDualEqualRankFunction_eq_scalar F ψ abv χ f f' Φ s a

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)] in
/-- The coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateCharacterModelOne_at_one :
    (modelMap πχ ℓχ (1 : ℂ)).val.val 1 = 1 := by
  change (πχ 1) (1 : ℂ) = 1
  simp

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)] in
/-- The trivial coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateTrivialModelOne_at_one :
    (modelMap π₁ ℓ₁ (1 : ℂ)).val.val 1 = 1 := by
  change (π₁ 1) (1 : ℂ) = 1
  simp

/-- At unit model vectors, only the row-to-scalar test transport remains. -/
theorem tateEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral abv μ
        (fun a => (χ a : ℂ)) 1 (tateScalarRowTest F Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateEqualRankIntegral_eq_scalar F ψ abv χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- The unit dual model vectors give exactly the inverse-character Mellin test. -/
theorem tateDualEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral abv μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 (tateScalarRowTest F Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateDualEqualRankIntegral_eq_scalar F ψ abv χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- Equality of the complete original rational-value families. -/
theorem tateEqualRankRationalValues_eq_scalar :
    equalRankRationalValues q ψ abv (rankOneQuotientHaar F) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q abv μ
        (fun a => (χ a : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ, ?_⟩
    have heq := funext (tateEqualRankIntegral_eq_scalar F ψ abv χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F Φ, ?_⟩
    rwa [tateEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- Equality of the complete dual rational-value families. -/
theorem tateDualEqualRankRationalValues_eq_scalar :
    dualEqualRankRationalValues q ψ abv (rankOneQuotientHaar F) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q abv μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ, ?_⟩
    have heq := funext (tateDualEqualRankIntegral_eq_scalar F ψ abv χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F Φ, ?_⟩
    rwa [tateDualEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- Absolute convergence is exactly integrability of the absorbed scalar test. -/
theorem tateEqualRankConverges_iff_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    EqualRankConverges ψ abv (rankOneQuotientHaar F) f.val f'.val Φ s ↔
      Integrable (scalarMellinIntegrand abv (fun a => (χ a : ℂ)) 1
        (tateCoefficientTest F ψ χ f f' Φ) s) μ := by
  rw [equalRankConverges_rankOneQuotientHaar_iff,
    ← integrable_tateScalarEquiv_iff F]
  simp_rw [tateEqualRankFunction_eq_scalar]
  rfl

/-- The dual absolute convergence is exactly inverse-character scalar integrability. -/
theorem tateDualEqualRankConverges_iff_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    EqualRankConverges (ψ.scale (-1)) abv (rankOneQuotientHaar F)
        (firstDualFunction ψ 0 f.val) (secondDualFunction ψ 0 f'.val) Φ s ↔
      Integrable (scalarMellinIntegrand abv (fun a => ((χ a)⁻¹ : ℂ)) 1
        (tateCoefficientTest F ψ χ f f' Φ) s) μ := by
  rw [equalRankConverges_rankOneQuotientHaar_iff,
    ← integrable_tateScalarEquiv_iff F]
  simp_rw [tateDualEqualRankFunction_eq_scalar]
  rfl

/-- The absorbed coefficient test identifies the complete actual model integral. -/
theorem tateEqualRankIntegral_eq_coefficientTest
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F) πχ π₁ ℓχ ℓ₁ f f' Φ =
      scalarMellinIntegral abv μ (fun a => (χ a : ℂ)) 1
        (tateCoefficientTest F ψ χ f f' Φ) :=
  funext (tateEqualRankIntegral_eq_scalar F ψ abv χ f f' Φ)

end Langlands.GodementJacquet
