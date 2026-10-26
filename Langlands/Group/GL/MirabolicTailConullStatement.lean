import Langlands.Group.GL.Padic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The open full-measure inverse-row tail locus

This is an internal geometric statement about actual general linear matrices.
The selected topology and its Borel measurable space are used throughout.
-/

namespace Langlands.GeneralLinear

open MeasureTheory

universe uF

/-- For every left Haar measure, the inverse last-row tail is nonzero on an
open set with null complement. Both block sizes may be zero. -/
def PadicMirabolicTailConullStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (a b : ℕ),
    letI := T.topology
    letI : MeasurableSpace (GeneralLinear (a + b + 1) F.Carrier) := borel _
    IsOpen {g : GeneralLinear (a + b + 1) F.Carrier |
      ∃ j : Fin (b + 1),
        (g⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) ≠ 0} ∧
    ∀ (μ : Measure (GeneralLinear (a + b + 1) F.Carrier)),
      μ.IsHaarMeasure →
      μ {g : GeneralLinear (a + b + 1) F.Carrier |
        ∀ j : Fin (b + 1),
          (g⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) = 0} = 0

end Langlands.GeneralLinear
