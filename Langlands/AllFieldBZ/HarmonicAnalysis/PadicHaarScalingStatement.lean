import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.HarmonicAnalysis.PadicHaarScalingStatement

/-!
# All-field port of `Langlands.HarmonicAnalysis.PadicHaarScalingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.HarmonicAnalysis.PadicHaarScalingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped NNReal
namespace Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement
universe uF

/-- Left and inverse-right multiplication on rectangular matrices has the
expected determinant factor, for every additive Haar measure. -/
def PadicRectangularHaarScalingStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    (r s : ℕ),
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      (μ : MeasureTheory.Measure (Matrix (Fin r) (Fin s) F.Carrier))
      [MeasureTheory.Measure.IsAddHaarMeasure μ]
      (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier),
      μ.map (fun X => (A : Matrix (Fin r) (Fin r) F.Carrier) * X *
        ((B⁻¹ : GeneralLinear s F.Carrier) : Matrix (Fin s) (Fin s) F.Carrier)) =
        (((T.determinantNorm r A : ℝ≥0) ^ s /
          (T.determinantNorm s B : ℝ≥0) ^ r)⁻¹) • μ

end Langlands.AllFieldBZ.HarmonicAnalysis
