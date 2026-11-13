import Langlands.Group.GL.BlockUnipotentHaarStatement
import Langlands.AllField.Group.GL.PadicBlocks
/-!
# Haar measure in upper block coordinates

This internal prerequisite states that a product of additive Haar measures on
the strict upper rectangular blocks transports to a Haar measure on the actual
block unipotent radical. It does not prove that assertion.
-/

namespace Langlands.AllField

universe uF

/-- Product additive Haar measure on the strict upper blocks, transported by the
published inverse coordinate map, is a Haar measure on the block radical. -/
def GLBlockUnipotentCoordinateHaarStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B : GeneralLinear.BlockShape n),
    letI := T.topology
    letI : ∀ ij : B.UpperPair,
        MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F) :=
      fun _ => borel _
    letI : MeasurableSpace (B.unipotentRadical F) := borel _
    ∀ (μ : (ij : B.UpperPair) →
        MeasureTheory.Measure
          (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F))
      [∀ ij, MeasureTheory.Measure.IsAddHaarMeasure (μ ij)],
      MeasureTheory.Measure.IsHaarMeasure
        ((MeasureTheory.Measure.pi μ).map (B.radicalCoordinates F).symm)

end Langlands.AllField
