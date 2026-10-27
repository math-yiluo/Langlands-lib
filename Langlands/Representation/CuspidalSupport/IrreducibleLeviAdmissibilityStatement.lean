import Langlands.Group.GL.Blocks
import Langlands.LocalField.Definitions
import Langlands.Representation.Category.Basic
import Mathlib.Basic.Complex.Basic

/-! BZ76 Theorem 3.25 for every actual standard product Levi. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- Every irreducible smooth complex representation of every actual standard
product Levi is admissible, for all ranks and block shapes, including the empty
product at rank zero. The carrier universe `uV` is independent of `uF`. -/
def IrreducibleLeviAdmissibilityTheorem {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    σ.IsIrreducible → σ.IsAdmissible

end Langlands.CuspidalSupport
