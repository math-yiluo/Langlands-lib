import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite

/-! Adjacent descents and the block order conditions on an actual permutation. -/

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

/-- The edges where a coordinate permutation decreases. -/
def permutationDescents (w : Equiv.Perm (Fin n)) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun i =>
    w (⟨i.val + 1, by omega⟩ : Fin n) < w (⟨i.val, by omega⟩ : Fin n)

@[simp] theorem mem_permutationDescents (w : Equiv.Perm (Fin n))
    (i : Fin (n - 1)) :
    i ∈ permutationDescents w ↔
      w (⟨i.val + 1, by omega⟩ : Fin n) < w (⟨i.val, by omega⟩ : Fin n) := by
  simp [permutationDescents]

private theorem strictMono_of_adjacent {m : ℕ} {α : Type*} [Preorder α]
    {f : Fin m → α} (h : ∀ a b, a.val + 1 = b.val → f a < f b) :
    StrictMono f := by
  cases m with
  | zero => exact fun a => Fin.elim0 a
  | succ m =>
    exact Fin.strictMono_iff_lt_succ.mpr fun i => h i.castSucc i.succ rfl

/-- A permutation increases inside every block exactly when none of its descents
joins two coordinates of that block. -/
theorem strictMono_blocks_iff_descents (B : BlockShape n) (w : Equiv.Perm (Fin n)) :
    (∀ j, StrictMono (fun a : Fin (B.size j) => w (B.index j a))) ↔
      ∀ i ∈ permutationDescents w,
        blockIndex B (⟨i.val, by omega⟩ : Fin n) ≠
          blockIndex B (⟨i.val + 1, by omega⟩ : Fin n) := by
  constructor
  · intro h i hi heq
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B (a := a) rfl
    obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq B (a := b) heq.symm
    have hxy : x < y := (index_strictMono B _).lt_iff_lt.mp (by
      rw [hx, hy]
      change i.val < i.val + 1
      omega)
    have hw := h _ hxy
    change w (B.index _ x) < w (B.index _ y) at hw
    rw [hx, hy] at hw
    exact (not_lt_of_gt hw) ((mem_permutationDescents w i).mp hi)
  · intro h j
    apply strictMono_of_adjacent
    intro a b hab
    have hval : (B.index j a).val + 1 = (B.index j b).val := by
      simp only [BlockShape.index, Function.Embedding.coeFn_mk, BlockShape.indexEquiv,
        Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
      omega
    let i : Fin (n - 1) := ⟨(B.index j a).val, by
      have hb := (B.index j b).isLt
      omega⟩
    have hleft : (⟨i.val, by omega⟩ : Fin n) = B.index j a := Fin.ext rfl
    have hright : (⟨i.val + 1, by omega⟩ : Fin n) = B.index j b := Fin.ext hval
    have hne : w (B.index j a) ≠ w (B.index j b) := by
      apply w.injective.ne
      apply (B.index j).injective.ne
      intro heq
      have := congrArg Fin.val heq
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt
    · have hi : i ∈ permutationDescents w := by
        rw [mem_permutationDescents, hleft, hright]
        exact hgt
      have hn := h i hi
      rw [hleft, hright, blockIndex_index, blockIndex_index] at hn
      exact (hn rfl).elim

/-- Both order clauses of a minimal representative are detected by adjacent descents. -/
theorem isMinimalRepresentative_iff_descents (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    IsMinimalRepresentative B C w ↔
      (∀ i ∈ permutationDescents w,
        blockIndex B (⟨i.val, by omega⟩ : Fin n) ≠
          blockIndex B (⟨i.val + 1, by omega⟩ : Fin n)) ∧
      (∀ i ∈ permutationDescents w.symm,
        blockIndex C (⟨i.val, by omega⟩ : Fin n) ≠
          blockIndex C (⟨i.val + 1, by omega⟩ : Fin n)) := by
  exact and_congr (strictMono_blocks_iff_descents B w)
    (strictMono_blocks_iff_descents C w.symm)

@[simp] theorem permutationDescents_one :
    permutationDescents (1 : Equiv.Perm (Fin n)) = ∅ := by
  ext i
  simp only [mem_permutationDescents, Equiv.Perm.one_apply, Fin.lt_def,
    Finset.notMem_empty, iff_false]
  omega

/-- The identity is the only permutation with no adjacent descent. -/
theorem permutationDescents_eq_empty_iff (w : Equiv.Perm (Fin n)) :
    permutationDescents w = ∅ ↔ w = 1 := by
  constructor
  · intro h
    have hw : StrictMono w := by
      apply strictMono_of_adjacent
      intro a b hab
      have hne : w a ≠ w b := w.injective.ne (by
        intro heq
        have := congrArg Fin.val heq
        omega)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlt
      · let i : Fin (n - 1) := ⟨a.val, by have := b.isLt; omega⟩
        have hleft : (⟨i.val, by omega⟩ : Fin n) = a := Fin.ext rfl
        have hright : (⟨i.val + 1, by omega⟩ : Fin n) = b := Fin.ext hab
        have hi : i ∈ permutationDescents w := by
          rw [mem_permutationDescents, hleft, hright]
          exact hgt
        rw [h] at hi
        exact (Finset.notMem_empty i hi).elim
    apply Equiv.ext
    intro a
    exact congrFun hw.eq_id a
  · rintro rfl
    exact permutationDescents_one

end Langlands.Geometric
