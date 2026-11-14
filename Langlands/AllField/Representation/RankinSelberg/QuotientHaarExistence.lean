import Langlands.Representation.RankinSelberg.QuotientHaarExistence
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# The JPSS quotient Haar existence statement

Specialize the constructed quotient measure to a p-adic field equipped with
the topology and valuation in its specified topological data.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply quotientHaarExistence
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- The published JPSS existence statement follows from the actual normalized
quotient measure and the proved right invariance of unipotent Haar measure. -/
theorem quotientHaarExistence 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    QuotientHaarExistenceStatement F T n := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  exact ⟨unipotentHaar_isMulRightInvariant F n,
    unipotent_compatibleMeasureExists F n⟩

-- Check the complete outer telescope of the published target.
end Langlands.AllField.RankinSelberg
