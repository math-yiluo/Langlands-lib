import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Group.GL.ReverseBlocks

/-!
# All-field port of `Langlands.Group.GL.ReverseBlocks`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.ReverseBlocks` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe u
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

variable (R : Type u) [CommRing R]

private theorem _root_.Langlands.GeneralLinear.BlockShape.reverseMatrix_conj_diagonal_iff (g : Langlands.GeneralLinear n R) :
    (∀ (i : Fin B.length) (a b : Fin (B.size i)),
      MulAut.conj (B.reverseMatrix R) g (B.index i a) (B.index i b) =
        if a = b then 1 else 0) ↔
    (∀ (i : Fin B.reverse.length) (a b : Fin (B.reverse.size i)),
      g (B.reverse.index i a) (B.reverse.index i b) = if a = b then 1 else 0) := by
  constructor
  · intro h i a b
    rw [← B.reverseMatrix_conjugate_entry R g i i a b]
    exact h i.rev a b
  · intro h i a b
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    rw [reverseMatrix_conjugate_entry]
    exact h i a b

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
