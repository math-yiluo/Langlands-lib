import Langlands.Representation.Category.Basic
import Langlands.Representation.Classification.Tempered

/-!
# Square-integrability at a chosen unitary normalization

This proposition states analytic square-integrability after removing any real
exponent equipped with an invariant positive form. It does not identify that
exponent with an essential square-integrability witness by definition.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every chosen unitary normalization of an irreducible essentially
square-integrable positive-rank representation is analytically square-integrable.
The invariant positive form in `d` is the only unitary normalization evidence. -/
def ChosenUnitarySquareIntegrability : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        T.IsEssentiallySquareIntegrable π.representation →
          ∀ d : UnitaryExponentData (T.determinantNorm n) π.representation,
            T.IsSquareIntegrable
              (realPowerTwist (T.determinantNorm n) (-d.exponent) π.representation)

end Langlands.Classification
