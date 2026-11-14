import Langlands.AllFieldBZ.Group.GL.MirabolicProjection
import Langlands.AllFieldBZ.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Derivative.PartialLocalizationData

/-!
# All-field port of `Langlands.Representation.Derivative.PartialLocalizationData`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.PartialLocalizationData` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Derivative.PartialLocalization
open Langlands.Derivative.PartialLocalization
open Langlands.GeneralLinear
universe uF

variable {F : Type uF} [CommRing F] {k m : ℕ}

private theorem _root_.Langlands.Derivative.PartialLocalization.mul_fixed_column (A B : Matrix (Fin (k + m)) (Fin (k + m)) F)
    (j : Fin k)
    (hB : ∀ i, B i (j.castAdd m) = if i = j.castAdd m then 1 else 0)
    (i : Fin (k + m)) :
    (A * B) i (j.castAdd m) = A i (j.castAdd m) := by
  simp only [Matrix.mul_apply, hB]
  simp

private theorem _root_.Langlands.Derivative.PartialLocalization.trailingBlock_mul (g h : GeneralLinear.upperUnipotent (k + m) F) :
    (g.val.val * h.val.val).submatrix (Fin.natAdd k) (Fin.natAdd k) =
      g.val.val.submatrix (Fin.natAdd k) (Fin.natAdd k) *
        h.val.val.submatrix (Fin.natAdd k) (Fin.natAdd k) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add]
  have hz : (∑ a : Fin k, g.val (i.natAdd k) (a.castAdd m) *
      h.val (a.castAdd m) (j.natAdd k)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [UpperUnipotent.entry_eq_zero g (by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega), zero_mul]
  rw [hz, zero_add]

private theorem _root_.Langlands.Derivative.PartialLocalization.trailingBlock_one :
    (1 : Matrix (Fin (k + m)) (Fin (k + m)) F).submatrix
      (Fin.natAdd k) (Fin.natAdd k) = 1 := by
  ext i j
  simp [Matrix.one_apply]

section Mirabolic
open Langlands.GeneralLinear.Mirabolic
end Mirabolic
section TwoBlocks
variable (hk : 0 < k) (hm : 0 < m)

end TwoBlocks
section Topology
variable [TopologicalSpace F]

end Topology
end Langlands.AllFieldBZ.Derivative.PartialLocalization
