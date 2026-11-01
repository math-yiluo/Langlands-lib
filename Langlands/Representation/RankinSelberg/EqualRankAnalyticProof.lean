import Langlands.Representation.RankinSelberg.ModelAsymptoticProof
import Langlands.Representation.RankinSelberg.QuotientAnalyticProof
import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.Representation.RankinSelberg.EqualRankUnitValueProof
import Langlands.Representation.RankinSelberg.NormalizedGeneratorExistenceProof
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.Representation.Whittaker.TypeAsymptoticProof

/-!
# Equal-rank JPSS convergence, rationality and normalized generator

Combine the full Whittaker expansion, finite-function Mellin analysis and quotient
Iwasawa integration with an actual unit-value test and Laurent normalization.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Equal-rank convergence, rational continuation, a common Laurent denominator
and a normalized reciprocal-polynomial generator for actual JPSS integrals. -/
theorem equalRankAnalytic
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    EqualRankAnalyticStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hexpπ := modelAsymptoticTransfer whittakerTypeAsymptotic.{uF, uV}
    p inferInstance F T n V π ψ (standardCharacter ψ n) (Or.inl rfl) hπ
  have hexpσ := modelAsymptoticTransfer whittakerTypeAsymptotic.{uF, uW}
    p inferInstance F T n W σ ψ (inverseStandardCharacter ψ n) (Or.inr rfl) hσ
  obtain ⟨D, hD, hdata⟩ :=
    equalRankQuotientAnalytic F T n finiteFunctionMellin.{uF}
      (quotientIwasawaIntegration F T n) V W π σ ψ
      hπ.1.1 hσ.1.1 hexpπ hexpσ
  obtain ⟨hconv, hrat, hclear⟩ := hdata ℓ ℓ' μ hμ
  have hden : HasCommonDenominator
      (equalRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ') := ⟨D, hD, hclear⟩
  have hone := equalRankUnitValue.{uF, uV, uW} F T n ψ μ hμ
    V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  exact ⟨hconv, hrat, hden,
    normalizedGeneratorExistence _ hden (mem_zetaSpan hone)⟩

end Langlands.RankinSelberg
