import Langlands.Representation.RankinSelberg.AnalyticBridge
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.WhittakerGammaAdaptersStatement
import Langlands.Representation.Whittaker.CharacterChange

/-!
# Proof of the Whittaker character and fixed-monomial epsilon adapters

This module proves `WhittakerGammaAdaptersStatement`: full standard and
inverse-standard Whittaker type agree for one representation, and a fixed
epsilon monomial for one nonzero functional pair at the constructed quotient
measure is an equal- or unequal-rank epsilon factor with the same monomial.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Full standard and inverse-standard Whittaker type agree for the same
representation: the functional spaces are linearly equivalent by the character
change at `-1`, and the other two conjuncts are unchanged. -/
theorem isOfWhittakerType_standard_iff_inverse :
    IsOfWhittakerType n (standardCharacter ψ n) π ↔
      IsOfWhittakerType n (inverseStandardCharacter ψ n) π := by
  have ec : glFunctionals ψ n π ≃ₗ[ℂ] glInverseFunctionals ψ n π := by
    have e := characterChangeFunctionalEquiv ψ π (-1)
    change glFunctionals ψ n π ≃ₗ[ℂ]
      functionals (upperUnipotent (n + 1) F) (standardCharacter (ψ.scale (-1)) n) π at e
    rw [standardCharacter_scale_neg_one] at e
    exact e
  constructor
  · rintro ⟨ha, hf, ⟨e⟩⟩
    exact ⟨ha, hf, ⟨ec.symm.trans e⟩⟩
  · rintro ⟨ha, hf, ⟨e⟩⟩
    exact ⟨ha, hf, ⟨ec.trans e⟩⟩

end Character

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}

/-- For a representation of Whittaker type, any two nonzero functionals have the
same coefficient model. -/
theorem coefficientModel_eq_of_whittakerType
    (hπ : IsOfWhittakerType n θ π)
    {ℓ ℓ' : functionals (upperUnipotent (n + 1) F) θ π}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    coefficientModel π ℓ = coefficientModel π ℓ' := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · obtain ⟨c, hc⟩ := hπ.eq_smul hℓ' ℓ
    rw [hc]
    exact coefficientModel_smul_le ℓ' c
  · obtain ⟨c, hc⟩ := hπ.eq_smul hℓ ℓ'
    rw [hc]
    exact coefficientModel_smul_le ℓ c

end Models

section Uniformity

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {c : ℂˣ} {m : ℤ}

/-- An equal-rank epsilon equation for one nonzero functional pair at the
constructed quotient measure gives the epsilon-factor relation for the same
coefficient and exponent. -/
theorem equalRankEpsilonFactor_of_equation
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hFE : EqualRankEpsilonEquation q ψ abv (unipotentQuotientHaar F n) ν π σ ℓ ℓ' c m) :
    IsEqualRankEpsilonFactor q ψ abv ν π σ (c, m) := by
  refine ⟨⟨unipotentHaar_isMulRightInvariant F n, unipotent_compatibleMeasureExists F n⟩,
    ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, ?_⟩
  intro hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  rw [unipotentQuotientHaar_unique F n μ hμ]
  exact (EqualRankEpsilonEquation.congr_model
    (coefficientModel_eq_of_whittakerType hπ hℓ hℓ₂)
    (coefficientModel_eq_of_whittakerType hσ hℓ' hℓ₂')).mp hFE

/-- The unequal-rank analogue: the supplied equation, with all of its
rectangular blocks, transports to every compatible measure and nonzero pair. -/
theorem unequalRankEpsilonFactor_of_equation
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hFE : UnequalRankEpsilonEquation hnr q ψ abv (unipotentQuotientHaar F n) ν
      π σ ℓ ℓ' c m) :
    IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ (c, m) := by
  refine ⟨⟨unipotentHaar_isMulRightInvariant F n, unipotent_compatibleMeasureExists F n⟩,
    ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, ?_⟩
  intro hinv μ hμ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
  rw [unipotentQuotientHaar_unique F n μ hμ]
  exact (UnequalRankEpsilonEquation.congr_model
    (coefficientModel_eq_of_whittakerType hπ hℓ hℓ₂)
    (coefficientModel_eq_of_whittakerType hσ hℓ' hℓ₂')).mp hFE

end Uniformity

/-- Proof of `WhittakerGammaAdaptersStatement`, with independent field and
representation-carrier universes. -/
theorem whittakerGammaAdapters :
    WhittakerGammaAdaptersStatement.{uF, uV, uW} := by
  refine ⟨?_, ?_, ?_⟩
  · intro F _ _ _ ψ n V _ _ π
    exact isOfWhittakerType_standard_iff_inverse ψ π
  · intro F _ _ _ _ _ _ n _ _ _ _ _ _ V _ _ W _ _ q ψ abv ν π σ
      hπ hσ ℓ ℓ' hℓ hℓ' c m hFE
    exact equalRankEpsilonFactor_of_equation hπ hσ hℓ hℓ' hFE
  · intro F _ _ _ _ _ _ n r hnr _ _ _ _ _ _ V _ _ W _ _ q ψ abv ν π σ
      hπ hσ ℓ ℓ' hℓ hℓ' c m hFE
    exact unequalRankEpsilonFactor_of_equation hnr hπ hσ hℓ hℓ' hFE

end Langlands.RankinSelberg
