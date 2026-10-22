import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# The JPSS quotient Haar existence statement

Specialize the constructed quotient measure to a p-adic field equipped with
the topology and valuation in its specified topological data.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- The published JPSS existence statement follows from the actual normalized
quotient measure and the proved right invariance of unipotent Haar measure. -/
theorem quotientHaarExistence {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    QuotientHaarExistenceStatement F T n := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  exact ⟨unipotentHaar_isMulRightInvariant F.Carrier n,
    unipotent_compatibleMeasureExists F.Carrier n⟩

-- Check the complete outer telescope of the published target.
example : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    Langlands.RankinSelberg.QuotientHaarExistenceStatement F T n :=
  @Langlands.RankinSelberg.quotientHaarExistence

end Langlands.RankinSelberg
