import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeProof
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Representation.RankinSelberg.PadicSymmetricLFactor
import Langlands.Representation.RankinSelberg.PadicGenericDualLFactor
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility
import Langlands.Representation.Whittaker.PadicCharacterIndependence

/-!
# Change of additive character for generic pair gamma factors

Pair L-polynomials do not depend on the additive Haar measure, and for generic `π`, `σ`
with central characters `ω_π`, `ω_σ` the gamma factors for `ψ` and for `ψ^b = ψ(b ·)`
(each with a self-dual measure) differ by the monomial
`ω_π(b)^(t+1) ω_σ(b)^(r+1) |b|^(-N/2) X^(N ord b)`, `N = (r+1)(t+1)`. Internal derivation
from the published epsilon and L-polynomial character-change results and the generic gamma
expression `γ = ε · L(1-s, π^∨ × σ^∨) / L(s, π × σ)`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

section PairRelation

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {P P' : ℂ[X]}

/-- Pair L-polynomials for two additive Haar measures agree: the block `j = 0` uses
the unit point mass on the empty rectangle, whatever the measure. -/
theorem IsPairLPolynomial.unique_of_measure {ν ν' : AdditiveHaarMeasure F}
    (h : IsPairLPolynomial q ψ abv μ ν π σ P)
    (h' : IsPairLPolynomial q ψ abv μ ν' π σ P') : P = P' := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr] at h h'
    have hr : r = n + (0 + (r - n - 1) + 1) := by omega
    have h0 := h 0 (r - n - 1) hr
    have h0' := h' 0 (r - n - 1) hr
    rw [rectangularMeasure_zero_rows] at h0 h0'
    exact h0.unique h0'
  · by_cases hrn : r = n
    · subst hrn
      rw [isPairLPolynomial_self] at h h'
      exact IsNormalizedGenerator.unique h h'
    · exact absurd h (not_isPairLPolynomial_of_lt (by omega))

end PairRelation

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic pair L-polynomial does not depend on the additive Haar measure. -/
theorem IsPadicPairLPolynomial.unique_of_measure {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν ν' : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {P P' : ℂ[X]} (h : IsPadicPairLPolynomial F ψ ν π σ P)
    (h' : IsPadicPairLPolynomial F ψ ν' π σ P') : P = P' := by
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
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).unique_of_measure (h'.2 μ hμ)

/-- The symmetric p-adic L-polynomial does not depend on the additive Haar measure. -/
theorem IsPadicSymmetricLPolynomial.unique_of_measure {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν ν' : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {P P' : ℂ[X]} (h : IsPadicSymmetricLPolynomial F ψ ν π σ P)
    (h' : IsPadicSymmetricLPolynomial F ψ ν' π σ P') : P = P' := by
  unfold IsPadicSymmetricLPolynomial at h h'
  split_ifs at h h'
  · exact h.unique_of_measure h'
  · exact h.unique_of_measure h'


/-- The epsilon character change in either rank relation. -/
theorem exists_isPadicSymmetricEpsilonFactor_characterChange {F : PadicField.{uF} p}
    {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ)
    (hπi : Representation.IsIrreducible π)
    (hπa : letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible π)
    (hσi : Representation.IsIrreducible σ)
    (hσa : letI := F.canonicalTopologicalData.topology; Langlands.IsAdmissible σ)
    (hωπ : Classification.HasGLCentralCharacter F.Carrier (r + 1) π ωπ)
    (hωσ : Classification.HasGLCentralCharacter F.Carrier (t + 1) σ ωσ)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a : F.Carrierˣ)
    (ν' : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData
      (letI := F.canonicalTopologicalData.topology
       letI := F.canonicalTopologicalData.valuativeRel
       letI := F.canonicalTopologicalData.localField
       ψ.scale a))
    (e : ℂˣ × ℤ) (he : IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e) :
    ∃ e' : ℂˣ × ℤ,
      IsPadicSymmetricEpsilonFactor F
        (letI := F.canonicalTopologicalData.topology
         letI := F.canonicalTopologicalData.valuativeRel
         letI := F.canonicalTopologicalData.localField
         ψ.scale a) ν'.val π σ e' ∧
      e'.2 = e.2 + ((r + 1) * (t + 1) : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) ∧
      (e'.1 : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (t + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
        ((F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^
          (-(((r + 1) * (t + 1) : ℕ) : ℂ) / 2) := by
  by_cases hrt : r = t
  · subst hrt
    exact equalRankEpsilonCharacterChange.{uF, uV, uW} p F r π σ ωπ ωσ hπi hπa hσi hσa
      hωπ hωσ ψ ν a ν' e he
  · exact pairFactorCharacterChange.{uF, uV, uW}.2 p F r t π σ ωπ ωσ hrt hπi hπa hσi hσa
      hωπ hωσ ψ ν a ν' e he

/-- The monomial by which a generic pair gamma factor changes when the additive
character `ψ` is replaced by `ψ^b`: `ω_π(b)^(t+1) ω_σ(b)^(r+1) |b|^(-N/2) X^(N ord b)`,
`N = (r+1)(t+1)`. -/
def gammaCharacterChangeMonomial (F : PadicField.{uF} p) (r t : ℕ)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ) (b : F.Carrierˣ) : RationalFunctions :=
  algebraMap ℂ RationalFunctions (((ωπ b : ℂˣ) : ℂ) ^ (t + 1) * ((ωσ b : ℂˣ) : ℂ) ^ (r + 1) *
      ((F.canonicalTopologicalData.normalizedAbs (b : F.Carrier) : ℝ) : ℂ) ^
        (-(((r + 1) * (t + 1) : ℕ) : ℂ) / 2)) *
    RatFunc.X ^ ((((r + 1) * (t + 1) : ℕ) : ℤ) * F.canonicalTopologicalData.ord (b : F.Carrier))

/-- **Change of additive character for generic pair gamma factors.** For generic
`π`, `σ` with central characters `ω_π`, `ω_σ`, gamma factors for `ψ` and for `ψ^b`
(with self-dual measures) differ by `gammaCharacterChangeMonomial`. -/
theorem genericGamma_characterChange {F : PadicField.{uF} p}
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν₀ : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (b : F.Carrierˣ)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData
      (letI := F.canonicalTopologicalData.topology
       letI := F.canonicalTopologicalData.valuativeRel
       letI := F.canonicalTopologicalData.localField
       ψ.scale b))
    {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ωπ ωσ : F.Carrierˣ →* ℂˣ)
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π)
    (hσ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ)
    (hωπ : Classification.HasGLCentralCharacter F.Carrier (r + 1) π ωπ)
    (hωσ : Classification.HasGLCentralCharacter F.Carrier (t + 1) σ ωσ)
    {G₀ G : RationalFunctions}
    (hG₀ : IsPadicSymmetricGammaFactor F ψ ν₀.val π σ G₀)
    (hG : IsPadicSymmetricGammaFactor F
      (letI := F.canonicalTopologicalData.topology
       letI := F.canonicalTopologicalData.valuativeRel
       letI := F.canonicalTopologicalData.localField
       ψ.scale b) ν.val π σ G) :
    G = gammaCharacterChangeMonomial F r t ωπ ωσ b * G₀ := by
  let := F.canonicalNormedField
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  -- genericity for the scaled character
  have hπ₁ : Whittaker.IsGeneric (ψ.scale b) r π :=
    (F.canonicalTopologicalData.isGeneric_iff_character π ψ (ψ.scale b)).mp hπ
  have hσ₁ : Whittaker.IsGeneric (ψ.scale b) t σ :=
    (F.canonicalTopologicalData.isGeneric_iff_character σ ψ (ψ.scale b)).mp hσ
  -- factors at ψ
  have he₀ := genericSymmetricEpsilonData_isPadic F ψ ν₀.val ν₀.property π σ hπ hσ
  have hP₀ := genericSymmetricLPolynomial_isPadic F ψ ν₀.val π σ hπ hσ
  have hD₀ := genericSymmetricDualLPolynomial_isPadic F ψ ν₀.val π σ hπ hσ
  set e₀ := genericSymmetricEpsilonData F ψ ν₀.val ν₀.property π σ hπ hσ
  set P₀ := genericSymmetricLPolynomial F ψ ν₀.val π σ hπ hσ
  set D₀ := genericSymmetricDualLPolynomial F ψ ν₀.val π σ hπ hσ
  have hγ₀ : G₀ = rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P₀ D₀ :=
    (symmetricGammaExpression.{uF, uV, uW} p F ψ ν₀ r t π σ
      (genericSymmetricGammaConstructionInput F ψ ν₀.val ν₀.property π σ hπ hσ)
      e₀ P₀ D₀ he₀ hP₀ hD₀ G₀).mp hG₀
  -- factors at ψ^b
  obtain ⟨e₁, he₁, he₁2, he₁1⟩ := exists_isPadicSymmetricEpsilonFactor_characterChange π σ
    ωπ ωσ hπ.1 hπ.2.1 hσ.1 hσ.2.1 hωπ hωσ ψ ν₀ b ν e₀ he₀
  have hP₁ : IsPadicSymmetricLPolynomial F (ψ.scale b) ν.val π σ P₀ := by
    have h1 := (Padic.isPadicSymmetricLPolynomial_characterChange F ψ b ν₀.val π σ P₀).mp hP₀
    have h2 := genericSymmetricLPolynomial_isPadic F (ψ.scale b) ν.val π σ hπ₁ hσ₁
    rwa [h2.unique_of_measure h1] at h2
  have hD₁ : IsPadicSymmetricLPolynomial F ((ψ.scale b).scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) D₀ := by
    have h1 := (Padic.isPadicSymmetricLPolynomial_characterChange F (ψ.scale (-1)) b ν₀.val
      _ _ D₀).mp hD₀
    rw [UnitaryAdditiveCharacter.scale_scale, mul_comm,
      ← UnitaryAdditiveCharacter.scale_scale] at h1
    have h2 := genericSymmetricDualLPolynomial_isPadic F (ψ.scale b) ν.val π σ hπ₁ hσ₁
    rwa [h2.unique_of_measure h1] at h2
  have hγ₁ : G = rationalGammaExpression (LocalFactor.residueReflection F) e₁.1 e₁.2 P₀ D₀ :=
    (symmetricGammaExpression.{uF, uV, uW} p F (ψ.scale b) ν r t π σ
      (genericSymmetricGammaConstructionInput F (ψ.scale b) ν.val ν.property π σ hπ₁ hσ₁)
      e₁ P₀ D₀ he₁ hP₁ hD₁ G).mp hG
  rw [hγ₀, hγ₁]
  unfold rationalGammaExpression gammaCharacterChangeMonomial
  simp only [coe_rationalEpsilonMonomial, he₁1, he₁2, map_mul]
  rw [zpow_add₀ (RatFunc.X_ne_zero)]
  ring

end Langlands.RankinSelberg
