import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Square integrability on a compact full central quotient -/

namespace Langlands

/-- On a compact quotient by the full group center, admissibility and a genuine
unitary central character imply square integrability for every Borel Haar measure. -/
def CompactCentralQuotientSquareIntegrabilityStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) (V : Type uV)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    [CompactSpace (G ⧸ Subgroup.center G)]
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (ρ : Representation ℂ G V),
    IsAdmissible ρ → Nonempty (UnitaryCentralCharacter ρ) →
    ∀ (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      IsSquareIntegrableModCenter ρ μ

end Langlands
