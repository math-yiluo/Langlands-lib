import Langlands.Representation.RankinSelberg.EqualRankUnitValueStatement
import Langlands.Representation.RankinSelberg.EqualRankCompactTest
import Langlands.Representation.Whittaker.WhittakerTypeKirillovProof

/-!
# An actual equal-rank JPSS integral with rational value one

Apply the proved Kirillov inclusion in both representation universes to the
compact coefficient-test construction, then normalize its actual integral.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Actual coefficient vectors and a Schwartz--Bruhat function give rational
value one for every compatible equal-rank quotient measure. -/
theorem equalRankUnitValue
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    EqualRankUnitValueStatement.{uF, uV, uW} F T n := by
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
  exact (hasEqualRankCompactTest_of_kirillov
    Langlands.whittakerTypeKirillov.{uF, uV}
    Langlands.whittakerTypeKirillov.{uF, uW}
    F T n ψ V W π σ hπ hσ ℓ ℓ' hℓ hℓ').one_mem_equalRankRationalValues
      hμ T.residueCardinality

end Langlands.RankinSelberg
