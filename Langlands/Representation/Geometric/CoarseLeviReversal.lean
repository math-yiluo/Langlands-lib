import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Tensor.FiniteRegrouping

/-! Coarse product-Levi reversal and its embedded matrix identities. -/

noncomputable section

namespace Langlands.OppositeCuspidalJacquetFiltration

open GeneralLinear

universe uF

section Levi

variable {R : Type uF} [CommRing R] {n : ℕ} (C : BlockShape n)

/-- The original Levi with reversed block labels, `m ↦ (i ↦ m i.rev)`. -/
def leviReverseEquiv : C.Levi R ≃* C.reverse.Levi R :=
  FiniteTensor.reindexGroup (fun i => GeneralLinear (C.size i) R) Fin.revPerm

@[simp]
theorem leviReverseEquiv_apply (m : C.Levi R) (i : Fin C.length) :
    leviReverseEquiv C m i = m i.rev := rfl

/-- Block reversal conjugates the reversed embedded Levi element onto the original one. -/
theorem reverseMatrix_mul_leviEmbedding (m : C.Levi R) :
    C.reverseMatrix R * C.reverse.leviEmbedding R (leviReverseEquiv C m) *
        (C.reverseMatrix R)⁻¹ = C.leviEmbedding R m := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := C.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := C.indexEquiv.surjective y
  obtain ⟨i, rfl⟩ := Fin.rev_surjective i
  obtain ⟨j, rfl⟩ := Fin.rev_surjective j
  change (MulAut.conj (C.reverseMatrix R)
      (C.reverse.leviEmbedding R (leviReverseEquiv C m))) (C.index i.rev a) (C.index j.rev b) =
    C.leviEmbedding R m (C.index i.rev a) (C.index j.rev b)
  rw [C.reverseMatrix_conjugate_entry R]
  by_cases hij : i = j
  · subst j
    exact (C.reverse.leviEmbedding_apply_same R (leviReverseEquiv C m)
      (i : Fin C.reverse.length) a b).trans (C.leviEmbedding_apply_same R m i.rev a b).symm
  · rw [C.reverse.leviEmbedding_apply_ne R _ a b hij,
      C.leviEmbedding_apply_ne R _ a b (fun h => hij (Fin.rev_injective h))]

theorem reverse_leviEmbedding_leviReverseEquiv (m : C.Levi R) :
    C.reverse.leviEmbedding R (leviReverseEquiv C m) =
      (C.reverseMatrix R)⁻¹ * C.leviEmbedding R m * C.reverseMatrix R := by
  rw [← reverseMatrix_mul_leviEmbedding C m]
  group

end Levi

end Langlands.OppositeCuspidalJacquetFiltration
