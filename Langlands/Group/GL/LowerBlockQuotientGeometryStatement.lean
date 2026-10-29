import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Analysis.Local.QuotientMeasure

/-!
# Geometry of the actual lower-block quotient chart

The open embedding, measurability and conullness conclusions extracted from
`LowerBlockQuotientDisintegrationStatement`, with the same canonical structures
and actual chart. This module states the geometry proposition; it proves none
of these conclusions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- The actual lower-block chart on the left unipotent quotient is an open
embedding, is measurable, and has conull range for every compatible measure
on the large quotient. The ranks are `a = n + 1` and `d = k + 1`. -/
def LowerBlockQuotientGeometryStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F.Carrier)) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1 + k + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
    let chart : LowerBlockQuotientParameters (n + 1) (k + 1) F.Carrier →
        LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier) :=
      lowerBlockQuotientChart
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1 + k))],
    ∀ (μ : Measure (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier))),
      IsCompatible (upperUnipotent (n + 1 + k + 1) F.Carrier)
        (generalLinearHaar F.Carrier (n + 1 + k)) (unipotentHaar F.Carrier (n + 1 + k)) μ →
      Topology.IsOpenEmbedding chart ∧ Measurable chart ∧ μ (Set.range chart)ᶜ = 0

end Langlands.RankinSelberg
