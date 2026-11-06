import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction

/-!
# Uniqueness of the real square-integrability exponent

Existence is part of essential square-integrability. Uniqueness follows from
the published comparison of two square-integrable twists on a nonzero vector.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

/-- An irreducible essentially square-integrable representation of positive
rank has exactly one real square-integrability exponent. -/
theorem essentialSquareIntegrabilityExponentUniqueness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    EssentialSquareIntegrabilityExponentUniqueness.{uF, uV} F T := by
  let := T.topology
  intro n hn π hi hess
  obtain ⟨s, hs⟩ := hess
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero π.representation hi
  exact ⟨s, hs, fun t ht => exponent_eq_of_isSquareIntegrable hn hv ht hs⟩

end Langlands.Classification
