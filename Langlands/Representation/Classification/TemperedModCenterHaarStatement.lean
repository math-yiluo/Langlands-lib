import Langlands.Representation.Classification.Tempered
import Langlands.Analysis.HaarLpStatement

/-!
# Haar normalization invariance of temperedness modulo the center

Both measures use the same supplied Borel measurable space on the actual
central quotient. Its local compactness and second countability are hypotheses.
-/

namespace Langlands

universe uG uV

/-- Temperedness modulo the center is unchanged by replacing a Haar measure on
the same locally compact, second-countable Borel central quotient. -/
def TemperedModCenterHaarInvariantStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace (G ⧸ Subgroup.center G)]
    [SecondCountableTopology (G ⧸ Subgroup.center G)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (ρ : Representation ℂ G V)
    (μ ν : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] [MeasureTheory.Measure.IsHaarMeasure ν],
    IsTemperedModCenter ρ μ ↔ IsTemperedModCenter ρ ν

end Langlands
