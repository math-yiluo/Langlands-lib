import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Geometric.WeylUniquenessStatement
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Hom.Set

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

theorem exists_index_of_blockIndex_eq (B : BlockShape n) {a : Fin n}
    {i : Fin B.length} (h : blockIndex B a = i) :
    ∃ b : Fin (B.size i), B.index i b = a := by
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective a
  simp only [blockIndex, Equiv.symm_apply_apply] at h
  subst i
  exact ⟨b, rfl⟩

theorem blockIndex_monotone (B : BlockShape n) : Monotone (blockIndex B) := by
  intro a b hab
  by_contra h
  have hlt : blockIndex B b < blockIndex B a := lt_of_not_ge h
  obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B (a := a) rfl
  obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq B (a := b) rfl
  have hba := B.index_lt_index_of_block_lt hlt y x
  rw [hx, hy] at hba
  exact (not_lt_of_ge hab) hba

private noncomputable def blockFiberEquiv (B : BlockShape n) (i : Fin B.length) :
    Fin (B.size i) ≃ {a : Fin n // blockIndex B a = i} :=
  Equiv.ofBijective (fun a => ⟨B.index i a, blockIndex_index B i a⟩) (by
    constructor
    · intro a b h
      exact (B.index i).injective (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B ha
      exact ⟨b, Subtype.ext hb⟩)

private noncomputable def blockPerm (B : BlockShape n) (b : Equiv.Perm (Fin n))
    (hb : b ∈ blockWeyl B) (i : Fin B.length) : Equiv.Perm (Fin (B.size i)) :=
  (blockFiberEquiv B i).trans
    ((b.subtypeEquiv (fun a => by
      change blockIndex B a = i ↔ blockIndex B (b a) = i
      rw [hb a])).trans (blockFiberEquiv B i).symm)

private theorem index_blockPerm (B : BlockShape n) (b : Equiv.Perm (Fin n))
    (hb : b ∈ blockWeyl B) (i : Fin B.length) (a : Fin (B.size i)) :
    B.index i (blockPerm B b hb i a) = b (B.index i a) := by
  exact congrArg Subtype.val ((blockFiberEquiv B i).apply_symm_apply
    (b.subtypeEquiv (fun a => by
      change blockIndex B a = i ↔ blockIndex B (b a) = i
      rw [hb a]) (blockFiberEquiv B i a)))

private theorem minimal_block_labels_eq (B C : BlockShape n)
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

private theorem minimal_eq_of_block_labels (B C : BlockShape n)
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

/-- A Weyl double coset contains at most one permutation increasing on the
source blocks with inverse increasing on the target blocks. -/
theorem weylDoubleCoset_injective (B C : BlockShape n) :
    Function.Injective (weylDoubleCoset B C) := by
  intro w v h
  obtain ⟨c, hc, b, hb, heq⟩ := DoubleCoset.eq.mp h
  apply Subtype.ext
  exact minimal_eq_of_block_labels B C w.val v.val w.property v.property
    (minimal_block_labels_eq B C w.val v.val w.property v.property c b hc hb heq)

/-- The closed uniqueness statement for all natural ranks. -/
theorem weylMinimalRepresentativeUniqueness :
    WeylMinimalRepresentativeUniquenessTheorem := by
  intro n B C
  exact weylDoubleCoset_injective B C

end Langlands.Geometric
