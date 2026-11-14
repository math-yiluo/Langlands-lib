import Langlands.AllFieldBZ.Group.GL.MirabolicProjection
import Langlands.Group.GL.MirabolicMixedProductSubgroups

/-!
# All-field port of `Langlands.Group.GL.MirabolicMixedProductSubgroups`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.MirabolicMixedProductSubgroups` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedProduct
open Langlands.GeneralLinear.Mirabolic.MixedProduct
universe u

variable {R : Type u} [CommRing R] {k r : ℕ}

/-! Concrete two-block calculations, including empty blocks. -/

namespace TwoBlock
open Langlands.GeneralLinear.Mirabolic.MixedProduct.TwoBlock
variable {a b : ℕ}

private def _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.TwoBlock.label : Fin a ⊕ Fin b → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

section Topology
variable [TopologicalSpace R]

end Topology
end TwoBlock
/-! The explicit coordinate permutations for the source's two embeddings. -/

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.left_diagonal_mem (g : leftSubgroup k r R) :
    (TwoBlock.projection (leftBlocks g)).2 ∈ Langlands.GeneralLinear.mirabolic r R := by
  intro j
  change g.val.val.val (leftIndex k r (Sum.inr (Fin.last r)))
    (leftIndex k r (Sum.inr j)) = _
  rw [leftIndex_last, g.val.property]
  simp only [← leftIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq, Sum.inr.injEq]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.right_diagonal_mem (g : rightSubgroup k r R) :
    (TwoBlock.projection (rightBlocks g)).1 ∈ Langlands.GeneralLinear.mirabolic r R := by
  intro j
  change g.val.val.val (rightIndex k r (Sum.inl (Fin.last r)))
    (rightIndex k r (Sum.inl j)) = _
  rw [rightIndex_last, g.val.property]
  simp only [← rightIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq, Sum.inl.injEq]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.reindex_mem_mirabolic {a b t : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin (t + 1)) (s : Fin a ⊕ Fin b) (he : e s = Fin.last t)
    (g : Matrix.GeneralLinearGroup (Fin a ⊕ Fin b) R)
    (hg : ∀ j, g.val s j = if j = s then 1 else 0) :
    Langlands.GeneralLinear.reindex e g ∈ Langlands.GeneralLinear.mirabolic t R := by
  intro j
  obtain ⟨j, rfl⟩ := e.surjective j
  rw [← he]
  change g.val (e.symm (e s)) (e.symm (e j)) = _
  simpa only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using hg j

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.leftBlocks_injective : Function.Injective (leftBlocks (k := k) (r := r) (R := R)) := by
  intro g h H
  apply Subtype.ext
  apply Subtype.ext
  exact (Langlands.GeneralLinear.reindex (leftIndex k r)).symm.injective (congrArg Subtype.val H)

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.rightBlocks_injective : Function.Injective (rightBlocks (k := k) (r := r) (R := R)) := by
  intro g h H
  apply Subtype.ext
  apply Subtype.ext
  exact (Langlands.GeneralLinear.reindex (rightIndex k r)).symm.injective (congrArg Subtype.val H)

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.right_B_last (g : rightSubgroup k r R) (j : Fin k) :
    TwoBlock.B (rightBlocks g) (Fin.last r) j = 0 := by
  change g.val.val.val (rightIndex k r (Sum.inl (Fin.last r)))
    (rightIndex k r (Sum.inr j)) = 0
  rw [rightIndex_last, g.val.property]
  simp only [← rightIndex_last (k := k) (r := r), Equiv.apply_eq_iff_eq,
    Sum.inr_ne_inl, ↓reduceIte]

private theorem _root_.Langlands.GeneralLinear.Mirabolic.MixedProduct.extend_rightOffDiagonal (g : rightSubgroup k r R) :
    extendRectangle (rightOffDiagonal g) = TwoBlock.B (rightBlocks g) := by
  ext i j
  exact Fin.lastCases (by simp [right_B_last]) (fun i => by
    simp [rightOffDiagonal, Matrix.submatrix_apply]) i

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.GeneralLinear.Mirabolic.MixedProduct
