import Langlands.AllFieldBZ.Group.GL.MirabolicRadical
import Langlands.Group.GL.MirabolicProjection

/-!
# All-field port of `Langlands.Group.GL.MirabolicProjection`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicProjection` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic
universe u

variable {F : Type u} [CommRing F] {n : ℕ}

/-- The defining last-row equations of a mirabolic matrix. -/
private theorem _root_.Langlands.GeneralLinear.Mirabolic.lastRow (g : Langlands.GeneralLinear.mirabolic n F) (j : Fin (n + 1)) :
    g.val.val (Fin.last n) j = if j = Fin.last n then 1 else 0 :=
  g.property j

/-- A product's upper-left block is the product of upper-left blocks when the
second factor has the mirabolic last row. -/
private theorem _root_.Langlands.GeneralLinear.Mirabolic.upperLeft_mul (g h : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hh : ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    (g * h).submatrix Fin.castSucc Fin.castSucc =
      g.submatrix Fin.castSucc Fin.castSucc * h.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hh, Fin.castSucc_ne_last]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.upperLeft_one :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
  ext i j
  simp [Matrix.one_apply]

section Topology
variable [TopologicalSpace F]

variable [IsTopologicalRing F]

end Topology
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic
