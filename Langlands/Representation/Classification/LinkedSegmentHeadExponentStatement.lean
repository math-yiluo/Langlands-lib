import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.Essential

/-!
# Exponent comparison for linked segment heads

An internal derived proposition relating actual special heads, arbitrary
positive-form unitary exponent witnesses, and the existing segment relations.
The scalar-character calculation and endpoint comparison are not proved here.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Linked nonprecedence gives the reversed weak exponent order, and precedence
forces strictly increasing exponents, for arbitrary unitary exponent witnesses
of the actual special heads. -/
def LinkedSegmentHeadExponentComparison : Prop :=
  letI := T.topology
  ∀ (Δ Γ : T.Segment.{max uF uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)),
    T.IsSegmentHead Δ π → T.IsSegmentHead Γ τ →
      ∀ (u : UnitaryExponentData (T.determinantNorm Δ.degree) π.representation)
        (v : UnitaryExponentData (T.determinantNorm Γ.degree) τ.representation),
        (Δ.IsLinked Γ → ¬ Δ.Precedes Γ → v.exponent ≤ u.exponent) ∧
          (Δ.Precedes Γ → u.exponent < v.exponent)

end Langlands.Classification
