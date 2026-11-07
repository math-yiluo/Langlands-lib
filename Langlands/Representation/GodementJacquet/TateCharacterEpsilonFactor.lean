import Langlands.Representation.GodementJacquet.TateRationalGaussFunctionalEquation
import Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation
import Langlands.Representation.GodementJacquet.TateCharacterNormalizer
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalFactor.Abelian.GaussDual

/-! The full scalar JPSS epsilon certificate with the actual abelian Gauss data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
private local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace F.Carrierˣ := borel _
private local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
private local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
private local instance : MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
private local instance : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "q" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The existing callable spectral epsilon never vanishes for the supplied Haar. -/
theorem tate_epsilon_ne_zero
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (s : ℂ) :
    LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure s ≠ 0 := by
  exact LocalFactor.PadicAbelian.epsilonAt_ne_zero T
    (LocalFactor.PadicAbelian.uniformizerUnit T) χ
    ((LocalFactor.PadicAbelian.conductorAt_iff T χ _).mpr rfl) ψ
    (F.canonicalTopologicalData.additiveConductor ψ) ν
    ((LocalFactor.PadicAbelian.additiveConductorAt_iff T ψ _).mpr rfl) s

/-- The actual unshifted Gauss constant, using its proved nonvanishing. -/
def tateEpsilonCoefficient
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) : ℂˣ :=
  Units.mk0 (LocalFactor.PadicAbelian.deligneConstant T χ ψ ν.measure)
    (tate_epsilon_ne_zero F ν χ ψ 0)

@[simp] theorem coe_tateEpsilonCoefficient
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) :
    (tateEpsilonCoefficient F ν χ ψ : ℂ) =
      LocalFactor.PadicAbelian.deligneConstant T χ ψ ν.measure := rfl

/-- The original JPSS monomial has precisely the callable abelian epsilon value. -/
theorem epsilonMonomial_tateEpsilonCoefficient
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (s : ℂ) :
    epsilonMonomial q (tateEpsilonCoefficient F ν χ ψ)
      (LocalFactor.PadicAbelian.epsilonExponent T χ ψ) s =
      LocalFactor.PadicAbelian.epsilon T χ ψ ν.measure s := by
  rw [epsilonMonomial, coe_tateEpsilonCoefficient, tate_spectralPoint_eq F]
  exact (LocalFactor.PadicAbelian.epsilon_eq_constant_mul_spectral_pow T χ ψ ν s).symm

private theorem tateRowTest_scalarRowTest (Φ : SchwartzBruhat (Fin 1 → F.Carrier)) :
    tateRowTest F.Carrier (tateScalarRowTest F.Carrier Φ) = Φ := by
  apply Subtype.ext
  funext x
  change Φ (fun _ => x 0) = Φ x
  apply congrArg (fun z : Fin 1 → F.Carrier => Φ z)
  funext i
  fin_cases i
  rfl

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (χ : Quasicharacter F.Carrier)

local notation "ρχ" => rankOneCharacter (χ : F.Carrierˣ →* ℂˣ)
local notation "ρ₁" => rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ)
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ

/-- The concrete Gauss data satisfy the original fixed-functional JPSS equation. -/
theorem tateCharacterEpsilonEquation
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    EqualRankEpsilonEquation q ψ abv (rankOneQuotientHaar F.Carrier) ν
      ρχ ρ₁ ℓχ ℓ₁ (tateEpsilonCoefficient F ν χ ψ)
      (LocalFactor.PadicAbelian.epsilonExponent T χ ψ) := by
  have hρχ := rankOneCharacter_isOfWhittakerType p F ψ χ
  have hρ₁ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) ρ₁ := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    exact rankOneCharacter_isOfWhittakerType p F ψ 1
  let := unipotentHaar_isMulRightInvariant F.Carrier 0
  obtain ⟨ζ, c, m, P, PDual, hζ, hP, hPDual, hFE⟩ :=
    equalRankFunctionalEquation.{uF, 0, 0} F T 0 ψ (rankOneQuotientHaar F.Carrier)
      (rankOneQuotientHaar_isCompatible F.Carrier) ν hν ℂ ℂ ρχ ρ₁ hρχ hρ₁ ℓχ ℓ₁
      (tateCharacterFunctional_ne_zero F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional_ne_zero ψ)
  rw [tateEqualRankRationalValues_eq_scalar F ψ χ] at hP
  rw [tateDualEqualRankRationalValues_eq_scalar F ψ χ] at hPDual
  have hP₀ := scalarMellin_character_isNormalizedGenerator F T χ
  have hPDual₀ : IsNormalizedGenerator
      (scalarMellinRationalValues q F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)⁻¹) 1)
      (LocalFactor.PadicAbelian.lPolynomial T χ⁻¹) := by
    simpa only [LocalFactor.PadicAbelian.quasicharacter_inv_coe] using
      scalarMellin_character_isNormalizedGenerator F T χ⁻¹
  obtain rfl := IsNormalizedGenerator.unique hP hP₀
  obtain rfl := IsNormalizedGenerator.unique hPDual hPDual₀
  refine ⟨ζ, LocalFactor.PadicAbelian.lPolynomial T χ,
    LocalFactor.PadicAbelian.lPolynomial T χ⁻¹, hζ, ?_, ?_, ?_⟩
  · rw [tateEqualRankRationalValues_eq_scalar F ψ χ]
    exact hP₀
  · rw [tateDualEqualRankRationalValues_eq_scalar F ψ χ]
    exact hPDual₀
  intro f f' Φ
  obtain ⟨Φhat, R, RDual, hFourier, hR, hRDual, _⟩ := hFE f f' Φ
  refine ⟨Φhat, R, RDual, hFourier, hR, hRDual, ?_⟩
  rw [funext (tateEqualRankIntegral_eq_scalar F ψ χ f f' Φ)] at hR
  rw [funext (tateDualEqualRankIntegral_eq_scalar F ψ χ f f' Φhat)] at hRDual
  let b : ℂ := f.val.val 1 * f'.val.val 1
  let Ψ := b • tateScalarRowTest F.Carrier Φ
  let Ψhat := b • tateScalarRowTest F.Carrier Φhat
  obtain ⟨g, hg, hGauss⟩ := tateRationalGaussFunctionalEquationStatement F ν ψ χ Ψ
  have hScalarFourier := tateScalarFourierPair_of_row ψ ν
    (tateScalarRowTest F.Carrier Φ) Φhat
    (by simpa only [tateRowTest_scalarRowTest F] using hFourier)
  have hg_eq : g = Ψhat := by
    apply Subtype.ext
    funext y
    calc
      g y = fourierIntegral ψ ν Ψ y := (hg y).2
      _ = b * fourierIntegral ψ ν (tateScalarRowTest F.Carrier Φ) y := by
        exact congrFun ((fourierTransform ψ ν).map_smul b
          (tateScalarRowTest F.Carrier Φ)) y
      _ = Ψhat y := by
        change b * fourierIntegral ψ ν (tateScalarRowTest F.Carrier Φ) y =
          b * tateScalarRowTest F.Carrier Φhat y
        rw [(hScalarFourier y).2]
  rw [hg_eq] at hGauss
  simp_rw [LocalFactor.PadicAbelian.quasicharacter_inv_coe] at hGauss
  intro s hRs hRDuals
  rw [pow_zero, one_mul, epsilonMonomial_tateEpsilonCoefficient F ν χ ψ]
  exact hGauss R RDual hR hRDual s hRs hRDuals

/-- The complete existing p-adic certificate has the actual Gauss data. -/
theorem isPadicPairEpsilonFactor_tateCharacter
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    IsPadicPairEpsilonFactor F ψ ν ρχ ρ₁
      (tateEpsilonCoefficient F ν χ ψ,
        LocalFactor.PadicAbelian.epsilonExponent T χ ψ) := by
  have hρχ := rankOneCharacter_isOfWhittakerType p F ψ χ
  have hρ₁ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) ρ₁ := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    exact rankOneCharacter_isOfWhittakerType p F ψ 1
  have hEq := tateCharacterEpsilonEquation F ψ χ ν hν
  rw [← unipotentQuotientHaar_zero F.Carrier] at hEq
  apply isPairEpsilonFactor_self.mpr
  exact equalRankEpsilonFactor_of_equation hρχ hρ₁
    (tateCharacterFunctional_ne_zero F.Carrier ψ (χ : F.Carrierˣ →* ℂˣ))
    (rankOneTrivialInverseFunctional_ne_zero ψ) hEq

/-- Concrete abelian data prove the full scalar JPSS epsilon relation. -/
def TateCharacterEpsilonFactorStatement : Prop :=
  ∀ (ν : AdditiveHaarMeasure F.Carrier) (ψ : UnitaryAdditiveCharacter F.Carrier),
    IsSelfDual ψ ν →
    ∀ χ : Quasicharacter F.Carrier,
      IsPadicPairEpsilonFactor F ψ ν
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
        (tateEpsilonCoefficient F ν χ ψ,
          LocalFactor.PadicAbelian.epsilonExponent T χ ψ)

theorem tateCharacterEpsilonFactorStatement : TateCharacterEpsilonFactorStatement F := by
  intro ν ψ hν χ
  exact isPadicPairEpsilonFactor_tateCharacter F ψ χ ν hν

end Langlands.GodementJacquet.Padic
