import Langlands.Representation.Classification.SquareIntegrableGenericityStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Full Whittaker type conditional on square-integrable genericity

This internal adapter statement concerns the original representation carrier.
The square-integrable genericity proposition remains an explicit input.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- Square-integrable genericity for the canonical topology implies full
standard Whittaker type for every irreducible square-integrable action on an
independently sized algebraic carrier. -/
def SquareIntegrableWhittakerTypeOfGenericityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p),
    Classification.SquareIntegrableGenericity.{uF,uV}
      F F.canonicalTopologicalData →
    ∀ (ψ : letI := F.canonicalTopologicalData.topology;
        UnitaryAdditiveCharacter F.Carrier)
      (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      Representation.IsIrreducible π →
      F.canonicalTopologicalData.IsSquareIntegrable π →
      (letI := F.canonicalTopologicalData.topology;
        IsOfWhittakerType n (standardCharacter ψ n) π)

end Langlands.RankinSelberg
