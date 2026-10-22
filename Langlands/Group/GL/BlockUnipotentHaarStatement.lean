import Langlands.Group.GL.BlockUnipotentCoordinates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Haar measure in upper block coordinates

This internal prerequisite states that a product of additive Haar measures on
the strict upper rectangular blocks transports to a Haar measure on the actual
block unipotent radical. It does not prove that assertion.
-/

namespace Langlands

universe uF

/-- Product additive Haar measure on the strict upper blocks, transported by the
published inverse coordinate map, is a Haar measure on the block radical. -/
def GLBlockUnipotentCoordinateHaarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (B : GeneralLinear.BlockShape n),
    letI := T.topology
    letI : ∀ ij : B.UpperPair,
        MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier) :=
      fun _ => borel _
    letI : MeasurableSpace (B.unipotentRadical F.Carrier) := borel _
    ∀ (μ : (ij : B.UpperPair) →
        MeasureTheory.Measure
          (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier))
      [∀ ij, MeasureTheory.Measure.IsAddHaarMeasure (μ ij)],
      MeasureTheory.Measure.IsHaarMeasure
        ((MeasureTheory.Measure.pi μ).map (B.radicalCoordinates F.Carrier).symm)

end Langlands
