import Langlands.AllField.Representation.RankinSelberg.UnequalRankCommonGeneratorProof
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.Representation.RankinSelberg.AnalyticBridge
import Langlands.Representation.RankinSelberg.WhittakerTypeFromMultiplicityProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof
import Langlands.Representation.Conductor.Essential
import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction

/-!
# The standard L-polynomial of a generic representation over every local field

For an irreducible admissible generic representation `π` of `GL_(n+2)(F)` over a
nonarchimedean local field of any characteristic, the rank-one character zeta values of
`π × 1` have a normalized polynomial generator `P`, i.e. `L(s, π) = P(q^(-s))⁻¹`
(JPSS 1983, Theorem (2.7)). The proof transports the all-field JPSS theorem
`Langlands.AllField.RankinSelberg.unequalRankCommonGenerator` to the ambient instances,
Borel structures and normalization used in Jacquet's setting.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.QuotientIntegration Polynomial

universe uF uV

section RankOne

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The identity functional on the trivial character of `GL₁`. -/
def rankOneIdentityFunctional (ψ : UnitaryAdditiveCharacter F) :
    glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)) :=
  ⟨LinearMap.id, by rw [glInverseFunctionals_rankOne]; trivial⟩

theorem rankOneIdentityFunctional_ne_zero (ψ : UnitaryAdditiveCharacter F) :
    (rankOneIdentityFunctional ψ).val ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (1 : ℂ)
  simp [rankOneIdentityFunctional] at this

end RankOne

/-! ### The standard L-polynomial -/

section Existence

/-- **Existence of the standard L-polynomial** (JPSS 1983, Theorem (2.7), for `π × 1`),
over every nonarchimedean local field, under Jacquet's normalizations `h`. -/
theorem exists_isCharacterLPolynomial_one (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (hπ : IsGeneric ψ (n + 1) π) :
    ∃ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P := by
  have hq := h.residueCardinality
  have hϖ := h.uniformizer
  have habv := h.abv_uniformizer
  have hunit := h.abv_unit
  have hB0 : BorelSpace (LeftUnipotentQuotient 0 F) := h.borel_rankOne
  clear h
  obtain rfl := hB0.measurable_eq
  obtain rfl := (inferInstance : BorelSpace (Langlands.GeneralLinear 1 F)).measurable_eq
  have habvT := AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ
    habv hunit
  have hqT : q = (LocalFieldData.ofInstances F).residueCardinality :=
    hq.trans AllField.RankinSelberg.residueCardinality_ofInstances.symm
  subst habvT hqT
  have hπW := isOfWhittakerType_of_isGeneric_localField hπ
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  have hσW : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) :=
    (isOfWhittakerType_standard_iff_inverse ψ _).mp
      (scalar_isOfWhittakerType_rankOne ψ _ rankOneCharacter_one_isSmooth)
  let mG : MeasurableSpace (Langlands.GeneralLinear 1 F) := borel _
  have bG : BorelSpace (Langlands.GeneralLinear 1 F) := ⟨rfl⟩
  let mQ : MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
  have bQ : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩
  let mF : MeasurableSpace F := borel F
  have bF : BorelSpace F := ⟨rfl⟩
  let mU : MeasurableSpace (upperUnipotent 1 F) := borel _
  have bU : BorelSpace (upperUnipotent 1 F) := ⟨rfl⟩
  have hcompat := rankOneQuotientHaar_isCompatible F
  let ν : AdditiveHaarMeasure F :=
    ⟨Measure.addHaar, inferInstance,
      HarmonicAnalysis.GeneralLocalField.haarMeasure_regular F Measure.addHaar⟩
  have hgen := AllField.RankinSelberg.unequalRankCommonGenerator.{uF, uV, 0} F
    (LocalFieldData.ofInstances F) 0 (n + 1)
  dsimp only [AllField.RankinSelberg.UnequalRankCommonGeneratorStatement,
    LocalFieldData.ofInstances] at hgen
  obtain ⟨P, hP⟩ := hgen (by omega) ψ (rankOneQuotientHaar F)
    hcompat ν V ℂ π (rankOneCharacter (1 : Fˣ →* ℂˣ))
    hπW hσW ℓ (rankOneIdentityFunctional ψ) hℓ (rankOneIdentityFunctional_ne_zero ψ)
  refine ⟨P, IsPairLPolynomial.isCharacterLPolynomial (ν := ν) ?_⟩
  rw [isPairLPolynomial_of_lt (by omega)]
  intro j k hr
  have hconv : ∀ (r : ℕ) (hr : r = 0 + (j + k + 1))
      (π' : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
      IsOfWhittakerType r (standardCharacter ψ r) π' →
      ∀ (ℓ₀ : glFunctionals ψ r π'), ℓ₀.val ≠ 0 →
      unequalRankZetaValuesAt j k hr (LocalFieldData.ofInstances F).residueCardinality ψ
          (AllField.RankinSelberg.normalizedAbsoluteValue (LocalFieldData.ofInstances F))
          (rankOneQuotientHaar F)
          (rectangularMeasure ν j (0 + 1)) π' (rankOneCharacter (1 : Fˣ →* ℂˣ)) =
        unequalRankValuesAt j k hr (LocalFieldData.ofInstances F).residueCardinality ψ
          (AllField.RankinSelberg.normalizedAbsoluteValue (LocalFieldData.ofInstances F))
          (rankOneQuotientHaar F)
          (rectangularMeasure ν j (0 + 1)) π' (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ₀
          (rankOneIdentityFunctional ψ) := by
    intro r hr π' hπ' ℓ₀ hℓ₀
    subst hr
    have han := AllField.RankinSelberg.unequalRankAnalytic.{uF, uV, 0} F
      (LocalFieldData.ofInstances F) 0 j k
    dsimp only [AllField.RankinSelberg.UnequalRankAnalyticStatement,
      LocalFieldData.ofInstances] at han
    exact (han ψ (rankOneQuotientHaar F) hcompat ν V ℂ π'
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) hπ' hσW ℓ₀ (rankOneIdentityFunctional ψ) hℓ₀
      (rankOneIdentityFunctional_ne_zero ψ)).zetaValues_eq hπ' hσW hℓ₀
      (rankOneIdentityFunctional_ne_zero ψ)
  rw [hconv (n + 1) hr π hπW ℓ hℓ]
  exact hP j k hr

end Existence

end Langlands.Conductor
