import Langlands.Representation.Category.Basic
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Renard's single-coefficient criterion without assumed admissibility

This is the general t.d.-group statement of Renard IV.3.2, Remark. Its conclusion
uses the coefficient condition from the source definition, without building
admissibility into either the hypothesis or the conclusion.
-/

noncomputable section

universe u v

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.3.2, Remark: for an irreducible smooth representation with a
unitary central character, one nonzero square-integrable smooth matrix
coefficient implies square-integrability of every smooth matrix coefficient.
The Haar measure on the actual central quotient is also right invariant.
Admissibility is not assumed. -/
def SingleCoefficientSquareIntegrabilityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : SmoothRep.{0, u, v} ℂ G), π.IsIrreducible →
    ∀ c : UnitaryCentralCharacter π.representation,
      (∃ (ℓ : SmoothDual π.representation) (x : π),
        matrixCoefficient π.representation ℓ x ≠ 0 ∧ MemLp (c.coefficientNorm ℓ x) 2 μ) →
      ∀ (m : SmoothDual π.representation) (y : π),
        MemLp (c.coefficientNorm m y) 2 μ

end Langlands.Renard.CompactRepresentation
