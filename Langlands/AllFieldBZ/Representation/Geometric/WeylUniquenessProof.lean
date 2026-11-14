import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.Geometric.WeylUniquenessProof

/-!
# All-field port of `Langlands.Representation.Geometric.WeylUniquenessProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.WeylUniquenessProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric
open Langlands.GeneralLinear
variable {n : ℕ}

private noncomputable def _root_.Langlands.Geometric.blockFiberEquiv (B : BlockShape n) (i : Fin B.length) :
    Fin (B.size i) ≃ {a : Fin n // blockIndex B a = i} :=
  Equiv.ofBijective (fun a => ⟨B.index i a, blockIndex_index B i a⟩) (by
    constructor
    · intro a b h
      exact (B.index i).injective (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B ha
      exact ⟨b, Subtype.ext hb⟩)

private noncomputable def _root_.Langlands.Geometric.blockPerm (B : BlockShape n) (b : Equiv.Perm (Fin n))
    (hb : b ∈ blockWeyl B) (i : Fin B.length) : Equiv.Perm (Fin (B.size i)) :=
  (blockFiberEquiv B i).trans
    ((b.subtypeEquiv (fun a => by
      change blockIndex B a = i ↔ blockIndex B (b a) = i
      rw [hb a])).trans (blockFiberEquiv B i).symm)

private theorem _root_.Langlands.Geometric.index_blockPerm (B : BlockShape n) (b : Equiv.Perm (Fin n))
    (hb : b ∈ blockWeyl B) (i : Fin B.length) (a : Fin (B.size i)) :
    B.index i (blockPerm B b hb i a) = b (B.index i a) := by
  exact congrArg Subtype.val ((blockFiberEquiv B i).apply_symm_apply
    (b.subtypeEquiv (fun a => by
      change blockIndex B a = i ↔ blockIndex B (b a) = i
      rw [hb a]) (blockFiberEquiv B i a)))

private theorem _root_.Langlands.Geometric.minimal_block_labels_eq (B C : BlockShape n)
    (w v : Equiv.Perm (Fin n)) (hw : IsMinimalRepresentative B C w)
    (hv : IsMinimalRepresentative B C v) (c b : Equiv.Perm (Fin n))
    (hc : c ∈ blockWeyl C) (hb : b ∈ blockWeyl B) (heq : v = c * w * b) :
    ∀ a, blockIndex C (w a) = blockIndex C (v a) := by
  have hi (i : Fin B.length) :
      (fun a => blockIndex C (w (B.index i a))) =
      (fun a => blockIndex C (v (B.index i a))) := by
    let f : Fin (B.size i) → Fin C.length := fun a => blockIndex C (w (B.index i a))
    have hm : Monotone f := (blockIndex_monotone C).comp (hw.1 i).monotone
    have he : f ∘ blockPerm B b hb i = fun a => blockIndex C (v (B.index i a)) := by
      funext a
      dsimp [f, Function.comp_def]
      rw [index_blockPerm, heq]
      exact (hc (w (b (B.index i a)))).symm
    have hm' : Monotone (f ∘ blockPerm B b hb i) := by
      rw [he]
      exact (blockIndex_monotone C).comp (hv.1 i).monotone
    have hs := Tuple.unique_monotone (σ := Equiv.refl _) (τ := blockPerm B b hb i)
      (show Monotone (f ∘ Equiv.refl _) from hm) hm'
    simpa only [Equiv.coe_refl, Function.comp_id, he] using hs
  intro a
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  exact congrFun (hi i) x

private theorem _root_.Langlands.Geometric.minimal_eq_of_block_labels (B C : BlockShape n)
    (w v : Equiv.Perm (Fin n)) (hw : IsMinimalRepresentative B C w)
    (hv : IsMinimalRepresentative B C v)
    (h : ∀ a, blockIndex C (w a) = blockIndex C (v a)) : w = v := by
  have hr (j : Fin C.length) :
      Set.range (fun a => w.symm (C.index j a)) =
      Set.range (fun a => v.symm (C.index j a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      have hx : blockIndex C (v (w.symm (C.index j a))) = j := by
        rw [← h, Equiv.apply_symm_apply, blockIndex_index]
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq C hx
      exact ⟨b, by simp only [hb, Equiv.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      have hx : blockIndex C (w (v.symm (C.index j a))) = j := by
        rw [h, Equiv.apply_symm_apply, blockIndex_index]
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq C hx
      exact ⟨b, by simp only [hb, Equiv.symm_apply_apply]⟩
  have hinv : w.symm = v.symm := by
    apply Equiv.ext
    intro x
    obtain ⟨⟨j, a⟩, rfl⟩ := C.indexEquiv.surjective x
    exact congrFun ((hw.2 j).eq_of_range_eq (hv.2 j) (hr j)) a
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hinv

end Langlands.AllFieldBZ.Geometric
