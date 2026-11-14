import Langlands.AllFieldBZ.Group.GL.BlockUnipotentCoordinates
import Langlands.Group.GL.BlockUnipotentHaarStatement

/-!
# All-field port of `Langlands.Group.GL.BlockUnipotentHaarStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockUnipotentHaarStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uF

/-- Product additive Haar measure on the strict upper blocks, transported by the
published inverse coordinate map, is a Haar measure on the block radical. -/
def GLBlockUnipotentCoordinateHaarStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ)
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

end Langlands.AllFieldBZ
