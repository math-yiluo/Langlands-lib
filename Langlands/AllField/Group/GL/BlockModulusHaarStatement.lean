import Langlands.Group.GL.BlockModulusHaarStatement
import Langlands.AllField.Group.GL.BlockModulus
/-!
# The explicit block modulus is the Haar module of Levi conjugation

Bernstein--Zelevinsky define `mod_U(m)` by the scaling of a Haar measure of the
unipotent radical `U` under `u ↦ m u m⁻¹`. This proposition states that the
published explicit block modulus `T.leviModulus B` is that module, for every
Borel Haar measure on the actual block unipotent radical. It is a proposition
definition, not a proof.
-/

open scoped NNReal

namespace Langlands.AllField

universe uF

/-- For every local-field realization, ordered block shape `B`, Borel Haar measure
`μ` on the actual block unipotent radical `U` and Levi element `m`, the image of `μ`
under conjugation `u ↦ m u m⁻¹` is `δ_P(m)⁻¹ μ`, where `δ_P = T.leviModulus B` is the
explicit block modulus. -/
def GLBlockModulusHaarStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ [MeasurableSpace (B.unipotentRadical F)]
      [BorelSpace (B.unipotentRadical F)]
      (μ : MeasureTheory.Measure (B.unipotentRadical F))
      [MeasureTheory.Measure.IsHaarMeasure μ] (m : B.Levi F),
      μ.map (B.leviAction F m) = ((T.leviModulus B m : ℝ≥0)⁻¹) • μ

end Langlands.AllField
