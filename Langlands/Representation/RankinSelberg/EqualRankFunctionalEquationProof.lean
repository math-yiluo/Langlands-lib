import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.EqualRankGammaExistenceStatement
import Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.LocalField.Normalization.Proof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.EqualRankGammaExistenceProof

/-! JPSS Theorem 2.7(iii), equal rank: gamma existence, normalization by the two
generators, the analytic theorem and row Fourier inversion. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

section Fourier

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [MeasurableSpace F] {d : ℕ}

/-- Closure and row inversion make the row Fourier transform surjective on test
functions: `Φ = F(F(F Ψ))` has transform `Ψ`, using inversion twice. -/
theorem exists_isRowFourierPair_of_selfDual {ψ : UnitaryAdditiveCharacter F}
    {ν : AdditiveHaarMeasure F} (hclosed : RowFourierClosed ψ ν d)
    (hinv : IsRowSelfDual ψ ν d) (Ψ : SchwartzBruhat (Fin d → F)) :
    ∃ Φ : SchwartzBruhat (Fin d → F), IsRowFourierPair ψ ν Φ Ψ := by
  obtain ⟨Ψ₁, h₁⟩ := hclosed Ψ
  obtain ⟨Ψ₂, h₂⟩ := hclosed Ψ₁
  obtain ⟨Φ, h₃⟩ := hclosed Ψ₂
  refine ⟨Φ, fun y => ?_⟩
  have e₁ : (Ψ₁ : (Fin d → F) → ℂ) = rowFourierIntegral ψ ν d Ψ := funext h₁
  have e₂ : (Ψ₂ : (Fin d → F) → ℂ) = rowFourierIntegral ψ ν d Ψ₁ := funext h₂
  have e₃ : (Φ : (Fin d → F) → ℂ) = rowFourierIntegral ψ ν d Ψ₂ := funext h₃
  rw [e₃, (hinv Ψ₂).2 y, h₂, e₁, (hinv Ψ).2 (-y), neg_neg]

end Fourier

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- An unnormalized equal-rank gamma equation, the two normalized generators and
row Fourier surjectivity give the normalized equal-rank functional equation. -/
theorem equalRankConclusion_of_gammaEquation (hq : 1 < q)
    (hclosed : RowFourierClosed ψ ν (n + 1)) (hinv : IsRowSelfDual ψ ν (n + 1))
    {G : RationalFunctions} (hG : EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G)
    {P Pdual : ℂ[X]}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (hPd : IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pdual) :
    EqualRankFunctionalEquationConclusion q ψ abv μ ν π σ ℓ ℓ' := by
  obtain ⟨ζ, hζ, -, hFE⟩ := hG
  obtain ⟨c, m, hcm⟩ := gammaNormalization_of_incidence hq ζ n G _ _ P Pdual hP hPd
    (by
      rintro R ⟨f, f', Φ, hR⟩
      obtain ⟨Φhat, R₁, Rd, -, hR₁, hRd, hN⟩ := hFE f f' Φ
      obtain rfl := hR.unique hq hR₁
      exact ⟨Rd, ⟨f, f', Φhat, hRd⟩, hN⟩)
    (by
      rintro Rd ⟨f, f', Ψ, hRd⟩
      obtain ⟨Φ, hΦΨ⟩ := exists_isRowFourierPair_of_selfDual hclosed hinv Ψ
      obtain ⟨Φhat, R, Rd₁, hΦ, hR, hRd₁, hN⟩ := hFE f f' Φ
      obtain rfl := hΦ.unique hΦΨ
      obtain rfl := hRd.unique hq hRd₁
      exact ⟨R, ⟨f, f', Φ, hR⟩, hN⟩)
  refine ⟨ζ, c, m, P, Pdual, hζ, hP, hPd, fun f f' Φ => ?_⟩
  obtain ⟨Φhat, R, Rd, hΦ, hR, hRd, hN⟩ := hFE f f' Φ
  exact ⟨Φhat, R, Rd, hΦ, hR, hRd, hcm R Rd hN⟩

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- JPSS Theorem 2.7(iii) for equal positive ranks: one model-minus-one scalar
and one epsilon monomial normalize the functional equation of every data. -/
theorem equalRankFunctionalEquation (n : ℕ) :
    EqualRankFunctionalEquationStatement.{uF, uV, uW} F T n := by
  have hS2 := equalRankGammaExistence.{uF, uV, uW} F T n
  have hA := equalRankAnalytic.{uF, uV, uW} F T n
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := equalRankGamma_valuative_nonarchimedean (K := F.Carrier)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
    borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ _ μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hq : 1 < T.residueCardinality := T.residueCardinality_gt_one
  obtain ⟨hclosed, hinv⟩ := HarmonicAnalysis.rowFourierCompatibility ψ ν (n + 1) hν
  obtain ⟨G, hG⟩ := hS2 ψ μ hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨P, hP⟩ := (hA ψ μ hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ').2.2.2
  obtain ⟨Pd, hPd⟩ := (hA (ψ.scale (-1)) μ hμ V W
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')).2.2.2
  rw [← dualEqualRankRationalValues_eq] at hPd
  exact equalRankConclusion_of_gammaEquation hq hclosed hinv hG hP hPd

end Padic

end Langlands.RankinSelberg
