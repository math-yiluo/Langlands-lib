import Langlands.Representation.MatrixCoefficient.SmoothSquareIntegrability

/-! # Failure of the single-coefficient criterion without irreducibility

This is the counterexample assertion in Renard IV.3.2, Remark. The negated
universal implication expresses existence of an actual smooth representation
with a unitary central character and a nonzero square-integrable coefficient,
which is neither irreducible nor square-integrable modulo its center.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.3.2, Remark: the single-coefficient criterion fails without
irreducibility. There is a nonirreducible smooth complex representation with
a unitary central character and a nonzero square-integrable smooth coefficient
that does not satisfy the source all-coefficients predicate. The assertion is
encoded as the negation of the corresponding universal implication. -/
def NonirreducibleSquareIntegrabilityCounterexampleStatement : Prop :=
  ¬ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : SmoothRep.{0, 0, 0} ℂ G), ¬ π.IsIrreducible →
    ∀ c : UnitaryCentralCharacter π.representation,
      (∃ (ℓ : SmoothDual π.representation) (x : π),
        matrixCoefficient π.representation ℓ x ≠ 0 ∧ MemLp (c.coefficientNorm ℓ x) 2 μ) →
      π.IsSquareIntegrableModuloCenter μ

end Langlands.Renard.CompactRepresentation
