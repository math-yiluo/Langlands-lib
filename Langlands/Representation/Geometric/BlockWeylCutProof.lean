import Langlands.Representation.Geometric.BlockWeylCutStatement

/-! A direct finite-coordinate proof of the block Weyl cut correspondence. -/

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

private theorem composition_prefix_sum (c : Composition n) (k : ℕ)
    (hk : k ≤ c.length) :
    (∑ j : Fin k, c.blocksFun (Fin.castLE hk j)) = c.sizeUpTo k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin k, c.blocksFun (Fin.castLE (by omega) j)) +
      c.blocksFun ⟨k, by omega⟩ = c.sizeUpTo (k + 1)
    rw [ih (by omega), c.sizeUpTo_succ' ⟨k, by omega⟩]

private theorem ofComposition_index (c : Composition n) (i : Fin c.length)
    (a : Fin (c.blocksFun i)) :
    (BlockShape.ofComposition c).index i a = c.embedding i a := by
  apply Fin.ext
  change ((BlockShape.ofComposition c).indexEquiv ⟨i, a⟩).val = _
  simp only [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, Composition.coe_embedding]
  change (∑ j : Fin i.val, c.blocksFun (Fin.castLE i.isLt.le j)) + a.val =
    c.sizeUpTo i.val + a.val
  rw [composition_prefix_sum]

private theorem blockIndex_ofComposition (c : Composition n) (a : Fin n) :
    blockIndex (BlockShape.ofComposition c) a = c.index a := by
  have h := blockIndex_index (BlockShape.ofComposition c) (c.index a) (c.invEmbedding a)
  rw [ofComposition_index, c.embedding_comp_inv] at h
  exact h

private theorem composition_index_lt_boundary (c : Composition n) (a : Fin n)
    (j : Fin (c.length + 1)) :
    (c.index a).val < j.val ↔ a.val < (c.boundary j).val := by
  change (c.index a).val < j.val ↔ a.val < c.sizeUpTo j.val
  have hu : a.val < c.sizeUpTo ((c.index a).val + 1) := by
    simpa only [Fin.val_succ] using c.lt_sizeUpTo_index_succ a
  constructor
  · intro h
    exact hu.trans_le
      (c.monotone_sizeUpTo (by omega))
  · intro h
    by_contra hn
    have hm := c.monotone_sizeUpTo (show j.val ≤ (c.index a).val by omega)
    have hl := c.sizeUpTo_index_le a
    omega

private theorem composition_index_eq_iff_boundaries (c : Composition n) (a b : Fin n) :
    c.index a = c.index b ↔
      ∀ j : Fin (c.length + 1), a.val < (c.boundary j).val ↔
        b.val < (c.boundary j).val := by
  simp_rw [← composition_index_lt_boundary]
  constructor
  · intro h j
    rw [h]
  · intro h
    apply le_antisymm
    · by_contra hn
      have h' := (h (c.index a).castSucc).mpr (show (c.index b).val <
        ((c.index a).castSucc).val from lt_of_not_ge hn)
      exact (lt_irrefl _) h'
    · by_contra hn
      have h' := (h (c.index b).castSucc).mp (show (c.index a).val <
        ((c.index b).castSucc).val from lt_of_not_ge hn)
      exact (lt_irrefl _) h'

private theorem ofComposition_blockIndex_eq_iff_cut_sides
    (c : Composition n) (a b : Fin n) :
    blockIndex (BlockShape.ofComposition c) a = blockIndex (BlockShape.ofComposition c) b ↔
      ∀ i ∈ (BlockShape.ofComposition c).cuts, a.val ≤ i.val ↔ b.val ≤ i.val := by
  rw [Fin.ext_iff]
  simp only [blockIndex_ofComposition]
  rw [← Fin.ext_iff (a := c.index a) (b := c.index b),
    composition_index_eq_iff_boundaries]
  constructor
  · intro h i hi
    rw [BlockShape.mem_cuts_iff, BlockShape.toComposition_ofComposition] at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
    have hs := h j
    have hv : (c.boundary j).val = i.val + 1 := congrArg Fin.val hj
    omega
  · intro h j
    by_cases h0 : c.boundary j = 0
    · simp only [h0, Fin.val_zero, Nat.not_lt_zero, iff_self]
    by_cases hn : c.boundary j = Fin.last n
    · simpa only [hn, Fin.val_last] using iff_of_true a.isLt b.isLt
    have hp : 0 < (c.boundary j).val := by
      have hne : (c.boundary j).val ≠ 0 := by
        simpa only [Fin.ext_iff, Fin.val_zero] using h0
      omega
    have hlt : (c.boundary j).val < n := by
      have hne : (c.boundary j).val ≠ n := by
        simpa only [Fin.ext_iff, Fin.val_last] using hn
      have hb := (c.boundary j).isLt
      omega
    let i : Fin (n - 1) := ⟨(c.boundary j).val - 1, by omega⟩
    have hi : i ∈ (BlockShape.ofComposition c).cuts := by
      rw [BlockShape.mem_cuts_iff, BlockShape.toComposition_ofComposition]
      apply Finset.mem_map.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      change (c.boundary j).val = (c.boundary j).val - 1 + 1
      omega
    have hs := h i hi
    change a.val ≤ (c.boundary j).val - 1 ↔ b.val ≤ (c.boundary j).val - 1 at hs
    omega

/-- Two coordinates have the same block label exactly when no cut separates them. -/
theorem blockIndex_eq_iff_cut_sides (B : BlockShape n) (a b : Fin n) :
    blockIndex B a = blockIndex B b ↔
      ∀ i ∈ B.cuts, a.val ≤ i.val ↔ b.val ≤ i.val := by
  obtain ⟨c, hc⟩ := (BlockShape.compositionEquiv n).symm.surjective B
  change BlockShape.ofComposition c = B at hc
  subst B
  exact ofComposition_blockIndex_eq_iff_cut_sides c a b

/-- The adjacent swap at an interior edge preserves blocks exactly at an uncut edge. -/
theorem adjacent_swap_mem_blockWeyl_iff (B : BlockShape n) (i : Fin (n - 1)) :
    Equiv.swap (⟨i.val, by omega⟩ : Fin n) (⟨i.val + 1, by omega⟩ : Fin n) ∈
      blockWeyl B ↔ i ∉ B.cuts := by
  let a : Fin n := ⟨i.val, by omega⟩
  let b : Fin n := ⟨i.val + 1, by omega⟩
  change Equiv.swap a b ∈ blockWeyl B ↔ i ∉ B.cuts
  have heq : blockIndex B a = blockIndex B b ↔ i ∉ B.cuts := by
    rw [blockIndex_eq_iff_cut_sides]
    constructor
    · intro h hi
      have hs := h i hi
      change (i.val ≤ i.val ↔ i.val + 1 ≤ i.val) at hs
      omega
    · intro h j hj
      have hne : i.val ≠ j.val := by
        intro hij
        have he : i = j := Fin.ext hij
        exact h (he ▸ hj)
      change i.val ≤ j.val ↔ i.val + 1 ≤ j.val
      omega
  constructor
  · intro h
    apply heq.mp
    have hs := h a
    rw [Equiv.swap_apply_left] at hs
    exact hs.symm
  · intro h x
    have hab := heq.mpr h
    by_cases hxa : x = a
    · subst x
      rw [Equiv.swap_apply_left]
      exact hab.symm
    by_cases hxb : x = b
    · subst x
      rw [Equiv.swap_apply_right]
      exact hab
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Subgroup inclusion of actual block-preserving permutations reverses cut inclusion. -/
theorem blockWeyl_le_iff_cuts_subset (B K : BlockShape n) :
    blockWeyl K ≤ blockWeyl B ↔ B.cuts ⊆ K.cuts := by
  constructor
  · intro h i hi
    by_contra hk
    have hs := h ((adjacent_swap_mem_blockWeyl_iff K i).mpr hk)
    exact ((adjacent_swap_mem_blockWeyl_iff B i).mp hs) hi
  · intro h w hw a
    apply (blockIndex_eq_iff_cut_sides B (w a) a).mpr
    have hs := (blockIndex_eq_iff_cut_sides K (w a) a).mp (hw a)
    intro i hi
    exact hs i (h hi)

/-- The closed block Weyl cut correspondence in every natural rank. -/
theorem blockWeylCutStatement : BlockWeylCutStatement := by
  constructor
  · intro n B i
    exact adjacent_swap_mem_blockWeyl_iff B i
  · intro n B K
    exact blockWeyl_le_iff_cuts_subset B K

end Langlands.Geometric
