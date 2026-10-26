import Langlands.Representation.RankinSelberg.EqualRankSwapEquations
import Langlands.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-! Universal factor-certificate transport at the original character. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory QuotientIntegration

universe uF uV uW

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  [BorelSpace (LeftUnipotentQuotient n F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (hLaw : ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (μ : Measure (LeftUnipotentQuotient n F)),
    IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ →
      HasCharacterChangeMeasureLaw abv (-1) μ)

include hπ hLaw

/-- Exchange all epsilon-certificate tests by the involutive translations of
the functionals. The existing compatible-measure witness is retained. -/
theorem IsEqualRankEpsilonFactor.negOne_swap {e : ℂˣ × ℤ}
    (h : IsEqualRankEpsilonFactor q ψ abv ν π σ e) :
    IsEqualRankEpsilonFactor q ψ abv ν σ π e := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ,
    ⟨negOneStandardFunctional ψ σ ℓ', negOneStandardFunctional_ne_zero ψ σ hℓ'⟩,
    ⟨negOneInverseFunctional ψ π ℓ, negOneInverseFunctional_ne_zero ψ π hℓ⟩, ?_⟩
  intro hinv μ hμc m m' hm hm'
  let ℓ₀ := negOneStandardFunctional ψ π m'
  let ℓ₀' := negOneInverseFunctional ψ σ m
  have hℓ₀ : ℓ₀.val ≠ 0 := negOneStandardFunctional_ne_zero ψ π hm'
  have hℓ₀' : ℓ₀'.val ≠ 0 := negOneInverseFunctional_ne_zero ψ σ hm
  obtain ⟨α, hα⟩ := exists_modelMinusOneScalar π hπ
  have ht := EqualRankEpsilonEquation.negOne_swap ψ abv μ (@hLaw hinv μ hμc)
    ν π σ ℓ₀ ℓ₀' (hα ℓ₀) hℓ₀' (@hall hinv μ hμc ℓ₀ ℓ₀' hℓ₀ hℓ₀')
  simpa only [ℓ₀, ℓ₀', negOneStandardFunctional_inverse,
    negOneInverseFunctional_standard] using ht

/-- Exchange every gamma-certificate test by the same functional translations,
retaining its nonzero rational-value witness. -/
theorem IsEqualRankGammaFactor.negOne_swap {G : RationalFunctions}
    (h : IsEqualRankGammaFactor q ψ abv ν π σ G) :
    IsEqualRankGammaFactor q ψ abv ν σ π G := by
  obtain ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩ := h
  refine ⟨hμ,
    ⟨negOneStandardFunctional ψ σ ℓ', negOneStandardFunctional_ne_zero ψ σ hℓ'⟩,
    ⟨negOneInverseFunctional ψ π ℓ, negOneInverseFunctional_ne_zero ψ π hℓ⟩, ?_⟩
  intro hinv μ hμc m m' hm hm'
  let ℓ₀ := negOneStandardFunctional ψ π m'
  let ℓ₀' := negOneInverseFunctional ψ σ m
  have hℓ₀ : ℓ₀.val ≠ 0 := negOneStandardFunctional_ne_zero ψ π hm'
  have hℓ₀' : ℓ₀'.val ≠ 0 := negOneInverseFunctional_ne_zero ψ σ hm
  obtain ⟨α, hα⟩ := exists_modelMinusOneScalar π hπ
  have ht := EqualRankGammaEquation.negOne_swap ψ abv μ (@hLaw hinv μ hμc)
    ν π σ ℓ₀ ℓ₀' (hα ℓ₀) hℓ₀' (@hall hinv μ hμc ℓ₀ ℓ₀' hℓ₀ hℓ₀')
  simpa only [ℓ₀, ℓ₀', negOneStandardFunctional_inverse,
    negOneInverseFunctional_standard] using ht

end Relations

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Fixed-character epsilon exchange for arbitrary equal-rank representations
of Whittaker type, at the same supplied additive Haar measure. -/
theorem isPadicPairEpsilonFactor_swap_equalRank
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    (e : ℂˣ × ℤ) :
    IsPadicPairEpsilonFactor F ψ ν π σ e ↔
      IsPadicPairEpsilonFactor F ψ ν σ π e := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  change IsPairEpsilonFactor _ _ _ _ _ _ _ ↔ IsPairEpsilonFactor _ _ _ _ _ _ _
  rw [isPairEpsilonFactor_self, isPairEpsilonFactor_self]
  have hLaw : ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue F.canonicalTopologicalData)
        (-1) μ := by
    intro hinv μ hμ
    exact characterChangeCompatibleMeasure p F F.canonicalTopologicalData n (-1) μ hμ
  exact ⟨IsEqualRankEpsilonFactor.negOne_swap _ ψ _ ν π σ hπ hLaw,
    IsEqualRankEpsilonFactor.negOne_swap _ ψ _ ν σ π hσ hLaw⟩

/-- Fixed-character gamma exchange obtained from the actual gamma equations,
without any analytic or factor-existence premise. -/
theorem isPadicPairGammaFactor_swap_equalRank
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hπ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    (G : RationalFunctions) :
    IsPadicPairGammaFactor F ψ ν π σ G ↔
      IsPadicPairGammaFactor F ψ ν σ π G := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  change IsPairGammaFactor _ _ _ _ _ _ _ ↔ IsPairGammaFactor _ _ _ _ _ _ _
  rw [isPairGammaFactor_self, isPairGammaFactor_self]
  have hLaw : ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) μ →
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue F.canonicalTopologicalData)
        (-1) μ := by
    intro hinv μ hμ
    exact characterChangeCompatibleMeasure p F F.canonicalTopologicalData n (-1) μ hμ
  exact ⟨IsEqualRankGammaFactor.negOne_swap _ ψ _ ν π σ hπ hLaw,
    IsEqualRankGammaFactor.negOne_swap _ ψ _ ν σ π hσ hLaw⟩

end Padic

end Langlands.RankinSelberg
