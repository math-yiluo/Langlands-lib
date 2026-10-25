import Langlands.Representation.Classification.LanglandsData

/-!
# Independent positive-rank tempered quotient coverage

This proposition is an internal proof-decomposition target. It requires an
actual quotient map onto the input representation and asserts no uniqueness.
-/

namespace Langlands.Classification

universe uF uV

/-- Every irreducible smooth representation of positive-rank `GL_n(F)` is
an actual quotient of a strictly ordered tempered standard module. -/
def TemperedLanglandsQuotientCoverage
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        ∃ t : T.TemperedLanglandsDatum.{max uF uV, uF} n,
          t.IsLanglandsQuotient π

end Langlands.Classification
