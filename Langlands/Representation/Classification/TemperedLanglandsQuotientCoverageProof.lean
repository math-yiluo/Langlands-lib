import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageStatement
import Langlands.Representation.Classification.TemperedQuotientAssembly
import Langlands.Representation.Classification.TemperedSmoothDualityProof
import Langlands.Representation.Classification.TwistedProductOrdinaryDualProof

/-!
# Independent positive-rank tempered quotient coverage: proof

The published analytic and ordinary product duality theorems discharge both
premises of the published quotient construction.
-/

namespace Langlands.Classification

universe uF uV

/-- Every irreducible smooth representation of positive-rank `GL_n(F)` is
an actual quotient of a strictly ordered tempered standard module. -/
theorem temperedLanglandsQuotientCoverage
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TemperedLanglandsQuotientCoverage.{uF, uV} F T :=
  temperedLanglandsQuotientCoverage_of.{uF, uV} F T
    padicTemperedSmoothDuality.{uF, max uF uV}
    (twistedProductOrdinaryDual.{uF, max uF uV} F T)

end Langlands.Classification
