import Langlands.Representation.Category.Basic
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # One square-integrable coefficient suffices (Renard IV.3.2, Remark)

An irreducible admissible representation with a unitary central character is square-integrable
modulo the centre as soon as one nonzero smooth matrix coefficient is.
-/

noncomputable section

universe u v

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.3.2, Remark, for admissible representations: let `G` be a t.d. group and `μ` a
Haar measure on `G / Z(G)`, also right invariant. Let `π` be an irreducible admissible smooth
representation with a unitary central character `c`. If some smooth matrix coefficient
`g ↦ ℓ(π(g) x)` is nonzero and square-integrable modulo the centre, then `π` is
square-integrable modulo the centre (the published `IsSquareIntegrableModCenter`). -/
def SquareIntegrableCoefficientCriterionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : SmoothRep.{0, u, v} ℂ G), π.IsIrreducible → π.IsAdmissible →
    ∀ c : UnitaryCentralCharacter π.representation,
      (∃ (ℓ : SmoothDual π.representation) (x : π),
        matrixCoefficient π.representation ℓ x ≠ 0 ∧ MemLp (c.coefficientNorm ℓ x) 2 μ) →
      IsSquareIntegrableModCenter π.representation μ

end Langlands.Renard.CompactRepresentation
