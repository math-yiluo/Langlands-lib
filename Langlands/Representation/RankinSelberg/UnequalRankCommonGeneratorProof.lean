import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof

/-! A normalized reciprocal polynomial common to every unequal-rank JPSS block. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

/-- Finite induction transports a block-zero generator through adjacent spans. -/
private theorem commonGenerator_of_adjacentSpan {n r : ℕ} (hnr : n < r)
    (values : (j k : ℕ) → r = n + (j + k + 1) → Set RationalFunctions)
    (hbase : NormalizedGeneratorExists (values 0 (r - n - 1) (by omega)))
    (hstep : ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
      zetaSpan (values (j + 1) k (by omega)) =
        zetaSpan (values j (k + 1) (by omega))) :
    ∃ P : Polynomial ℂ, ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator (values j k hr) P := by
  obtain ⟨P, hP⟩ := hbase
  refine ⟨P, ?_⟩
  intro j
  induction j with
  | zero =>
      intro k hr
      have hk : k = r - n - 1 := by omega
      subst k
      exact hP
  | succ j ih =>
      intro k hr
      have hspan := hstep j k (by omega)
      have hgen := ih (k + 1) (by omega)
      exact ⟨hgen.1, hspan.trans hgen.2⟩

/-- JPSS Theorem 2.7(ii): one normalized reciprocal polynomial generates every
allowed block at fixed unequal ranks, for the supplied topology and measures. -/
theorem unequalRankCommonGenerator.{uF,uV,uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankCommonGeneratorStatement.{uF,uV,uW} F T n r := by
  have hanalytic : ∀ j k, UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k :=
    fun j k => unequalRankAnalytic.{uF,uV,uW} F T n j k
  have hadjacent := unequalRankAdjacentBlockSpan.{uF,uV,uW} F T n r
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  dsimp only [UnequalRankCommonGeneratorStatement,
    UnequalRankAnalyticStatement, UnequalRankAdjacentBlockSpanStatement] at *
  intro hnr ψ hright μ hμ ν V instV modV W instW modW π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hbase : NormalizedGeneratorExists
      (unequalRankValuesAt 0 (r - n - 1) (by omega) T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ') := by
    have hgeneral : ∀ (r : ℕ) (hr : r = n + (0 + (r - n - 1) + 1))
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        ∀ (ℓ : glFunctionals ψ r π), ℓ.val ≠ 0 →
        NormalizedGeneratorExists
          (unequalRankValuesAt 0 (r - n - 1) hr T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ') := by
      intro r hr π hπ ℓ hℓ
      generalize hk : r - n - 1 = k at *
      subst r
      exact (hanalytic 0 k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').2.2.2
    exact hgeneral r (by omega) π hπ ℓ hℓ
  exact commonGenerator_of_adjacentSpan hnr
    (fun j k hr => unequalRankValuesAt j k hr T.residueCardinality ψ
      (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ')
    hbase (hadjacent hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')

end Langlands.RankinSelberg
