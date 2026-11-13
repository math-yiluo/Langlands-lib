import Langlands.Representation.Classification.TadicComplementaryEndpointBridge
import Langlands.Representation.Unitary.CharacterLimitSubquotientsProof

/-!
# Tadić's complementary-series proposition (Tadić 1986, Proposition 2.9)

This module proves `ComplementarySeriesUnitarity` unconditionally. It combines the
bridge `complementarySeriesUnitarity_of_characterLimit` with the Library proof of
`UnitaryCharacterLimitSubquotientsStatement`.
-/

namespace Langlands.Classification

universe uF uV

/-- Tadić 1986, Proposition 2.9: unitarity of the complementary series on the open
interval and of every irreducible constituent at its end point. -/
theorem complementarySeriesUnitarity {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : ComplementarySeriesUnitarity.{uF, uV} F T :=
  complementarySeriesUnitarity_of_characterLimit F T
    Langlands.unitaryCharacterLimitSubquotients.{uF, max uF uV}

end Langlands.Classification
