import Langlands.Representation.GodementJacquet.LocalTateModelTransport
import Langlands.Representation.RankinSelberg.EpsilonFactor

/-! Transport of supplied scalar Tate data to the actual rank-one JPSS relation. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear QuotientIntegration

universe uF uG

section ScalarData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ]

/-- Actual scalar analytic and functional-equation conclusions supplied to the
transport. This predicate does not assert that the scalar theory holds. -/
def ScalarTateEpsilonData (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure Fˣ) (ν : AdditiveHaarMeasure F)
    (χ : Fˣ →* ℂˣ) (c : ℂˣ) (m : ℤ) : Prop :=
  ScalarMellinAnalyticData q abv μ (fun a => (χ a : ℂ)) 1 ∧
  ScalarMellinAnalyticData q abv μ (fun a => ((χ a)⁻¹ : ℂ)) 1 ∧
  ∃ P Pdual : Polynomial ℂ,
    IsNormalizedGenerator (scalarMellinRationalValues q abv μ (fun a => (χ a : ℂ)) 1) P ∧
    IsNormalizedGenerator (scalarMellinRationalValues q abv μ (fun a => ((χ a)⁻¹ : ℂ)) 1)
      Pdual ∧
    ∀ Φ : SchwartzBruhat F, ∃ Φhat : SchwartzBruhat F,
      (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
        Φhat y = fourierIntegral ψ ν Φ y) ∧
      ∀ R Rdual : RationalFunctions,
        HasRationalContinuation q (scalarMellinIntegral abv μ (fun a => (χ a : ℂ)) 1 Φ) R →
        HasRationalContinuation q
          (scalarMellinIntegral abv μ (fun a => ((χ a)⁻¹ : ℂ)) 1 Φhat) Rdual →
        NormalizedFunctionalEquation q P Pdual 1 c 0 m R Rdual

end ScalarData

section Fourier

variable (F : Type uF) [TopologicalSpace F]

/-- The row and scalar test pullbacks are inverse in both directions. -/
@[simp] theorem tateRowTest_tateScalarRowTest (Φ : SchwartzBruhat (Fin 1 → F)) :
    tateRowTest F (tateScalarRowTest F Φ) = Φ := by
  apply Subtype.ext
  funext x
  change Φ (fun _ => x 0) = Φ x
  apply congrArg (fun y => Φ y)
  funext i
  fin_cases i
  rfl

variable [Field F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]

/-- The scalar plus-Fourier integral is complex-linear in its test. -/
theorem tateFourierIntegral_smul (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (C : ℂ) (Φ : SchwartzBruhat F) (y : F) :
    fourierIntegral ψ ν (C • Φ) y = C * fourierIntegral ψ ν Φ y := by
  exact congrArg (fun g : F → ℂ => g y) ((fourierTransform ψ ν).map_smul C Φ)

end Fourier

section Equation

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F) (χ : Fˣ →* ℂˣ) (c : ℂˣ) (m : ℤ)

local notation "πχ" => rankOneCharacter χ
local notation "π₁" => rankOneCharacter (1 : Fˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F ψ χ
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ
local notation "μ" => localMultiplicativeHaar F

/-- Supplied scalar Tate conclusions yield the fixed-functional JPSS equation
with exactly the same epsilon coefficient and exponent. -/
theorem tateEqualRankEpsilonEquation_of_scalar
    (h : ScalarTateEpsilonData q ψ abv μ ν χ c m) :
    EqualRankEpsilonEquation q ψ abv (rankOneQuotientHaar F) ν
      πχ π₁ ℓχ ℓ₁ c m := by
  obtain ⟨hA, hAd, P, Pd, hP, hPd, hFE⟩ := h
  refine ⟨1, P, Pd, rankOneTrivialModel_minusOne ψ ℓ₁, ?_, ?_, ?_⟩
  · rwa [tateEqualRankRationalValues_eq_scalar]
  · rwa [tateDualEqualRankRationalValues_eq_scalar]
  · intro f f' Φ
    obtain ⟨Ψ, hΨ, -⟩ := hFE (tateScalarRowTest F Φ)
    let Φhat := tateRowTest F Ψ
    have hrow : IsRowFourierPair ψ ν Φ Φhat := by
      intro y
      change Ψ (y 0) = rowFourierIntegral ψ ν 1 Φ y
      rw [← tateRowTest_tateScalarRowTest F Φ, rowFourierIntegral_tateRowTest]
      exact (hΨ (y 0)).2
    obtain ⟨Ψc, hΨc, hFEc⟩ := hFE (tateCoefficientTest F ψ χ f f' Φ)
    have htest : Ψc = tateCoefficientTest F ψ χ f f' Φhat := by
      apply Subtype.ext
      funext y
      change Ψc y = (f.val.val 1 * f'.val.val 1) * Ψ y
      rw [(hΨc y).2, (hΨ y).2]
      exact tateFourierIntegral_smul F ψ ν _ _ y
    obtain ⟨R, hR⟩ := hA.2.1 (tateCoefficientTest F ψ χ f f' Φ)
    obtain ⟨Rd, hRd⟩ := hAd.2.1 Ψc
    refine ⟨Φhat, R, Rd, hrow, ?_, ?_, hFEc R Rd hR hRd⟩
    · rwa [tateEqualRankIntegral_eq_coefficientTest]
    · have heq := funext (tateDualEqualRankIntegral_eq_scalar F ψ abv χ f f' Φhat)
      rw [heq]
      simpa only [htest, tateCoefficientTest] using hRd

end Equation

section Models

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
  {ρ : Representation ℂ G ℂ}

/-- On the complex scalar carrier, every nonzero equivariant functional has the
same actual coefficient image. No smoothness hypothesis is needed. -/
theorem coefficientModel_eq_of_nonzero_complex_forms
    (ℓ ℓ' : functionals N θ ρ) (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    coefficientModel ρ ℓ = coefficientModel ρ ℓ' := by
  have hcoord (L : Module.Dual ℂ ℂ) (z : ℂ) : L z = z * L 1 := by
    calc L z = L (z • (1 : ℂ)) := by simp
      _ = z * L 1 := by rw [map_smul, smul_eq_mul]
  have hscale (L L' : functionals N θ ρ) (hL : L.val ≠ 0) :
      L' = (L'.val 1 / L.val 1) • L := by
    have h1 : L.val 1 ≠ 0 := by
      intro h1
      apply hL
      apply LinearMap.ext
      intro z
      rw [hcoord, h1, mul_zero]
      rfl
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    change L'.val z = (L'.val 1 / L.val 1) * L.val z
    rw [hcoord L'.val z, hcoord L.val z]
    field_simp [h1]
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · nth_rw 1 [hscale ℓ' ℓ hℓ']
    exact coefficientModel_smul_le ℓ' _
  · nth_rw 1 [hscale ℓ ℓ' hℓ]
    exact coefficientModel_smul_le ℓ _

end Models

section EpsilonFactor

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F) (χ : Fˣ →* ℂˣ) (c : ℂˣ) (m : ℤ)

local notation "πχ" => rankOneCharacter χ
local notation "π₁" => rankOneCharacter (1 : Fˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F ψ χ
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ

/-- The supplied scalar coefficient and exponent satisfy the full JPSS relation,
including every compatible measure and every pair of nonzero functionals. -/
theorem tateIsEqualRankEpsilonFactor_of_scalar
    (h : ScalarTateEpsilonData q ψ abv (localMultiplicativeHaar F) ν χ c m) :
    IsEqualRankEpsilonFactor q ψ abv ν πχ π₁ (c, m) := by
  have hχ := tateCharacterFunctional_ne_zero F ψ χ
  have h₁ := rankOneTrivialInverseFunctional_ne_zero ψ
  refine ⟨⟨unipotentHaar_rankOne_rightInvariant F, rankOne_compatibleMeasureExists F⟩,
    ⟨ℓχ, hχ⟩, ⟨ℓ₁, h₁⟩, ?_⟩
  intro hinv μ hμ ℓ ℓ' hℓ hℓ'
  rw [eq_rankOneQuotientHaar_of_isCompatible F μ hμ]
  exact (EqualRankEpsilonEquation.congr_model
    (coefficientModel_eq_of_nonzero_complex_forms ℓχ ℓ hχ hℓ)
    (coefficientModel_eq_of_nonzero_complex_forms ℓ₁ ℓ' h₁ hℓ')).mp
      (tateEqualRankEpsilonEquation_of_scalar F q ψ abv ν χ c m h)

/-- The same scalar data give the actual pair epsilon factor in rank one. -/
theorem tateIsPairEpsilonFactor_of_scalar
    (h : ScalarTateEpsilonData q ψ abv (localMultiplicativeHaar F) ν χ c m) :
    IsPairEpsilonFactor q ψ abv ν πχ π₁ (c, m) := by
  rw [isPairEpsilonFactor_self]
  exact tateIsEqualRankEpsilonFactor_of_scalar F q ψ abv ν χ c m h

end EpsilonFactor

end Langlands.GodementJacquet
