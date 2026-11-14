import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Group.GL.BlockModulusHaarStatement

/-!
# All-field port of `Langlands.Group.GL.BlockModulusHaarStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockModulusHaarStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped NNReal
namespace Langlands.AllFieldBZ
universe uF

/-- For every p-adic field realization, ordered block shape `B`, Borel Haar measure
`μ` on the actual block unipotent radical `U` and Levi element `m`, the image of `μ`
under conjugation `u ↦ m u m⁻¹` is `δ_P(m)⁻¹ μ`, where `δ_P = T.leviModulus B` is the
explicit block modulus. -/
def GLBlockModulusHaarStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ)
    (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ [MeasurableSpace (B.unipotentRadical F.Carrier)]
      [BorelSpace (B.unipotentRadical F.Carrier)]
      (μ : MeasureTheory.Measure (B.unipotentRadical F.Carrier))
      [MeasureTheory.Measure.IsHaarMeasure μ] (m : B.Levi F.Carrier),
      μ.map (B.leviAction F.Carrier m) = ((T.leviModulus B m : ℝ≥0)⁻¹) • μ

end Langlands.AllFieldBZ
