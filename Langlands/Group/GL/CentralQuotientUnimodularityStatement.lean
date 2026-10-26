import Langlands.Representation.Classification.Tempered

/-!
# Right invariance of Haar measures on actual p-adic GL central quotients

This closed proposition uses the supplied field topology and its Borel
measurable space on the quotient by the full group center.
-/

namespace Langlands

universe uF

/-- Every Haar measure on the actual full central quotient of a positive-rank
p-adic general linear group is right invariant for the supplied topology. -/
def GLCentralQuotientHaarRightInvariantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      letI := T.centralQuotientMeasurableSpace n
      ∀ (μ : MeasureTheory.Measure
          (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
        [μ.IsHaarMeasure], MeasureTheory.Measure.IsMulRightInvariant μ

end Langlands
