import Langlands.Representation.Geometric.BlockShapeCuts

/-! Interior boundary coordinates and the number of edges inside blocks. -/

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ}

/-- Regard an interior cut as its positive boundary position, with endpoints omitted. -/
def interiorBoundary (n : ℕ) : Fin (n - 1) ↪ Fin (n + 1) where
  toFun i := ⟨i.val + 1, by omega⟩
  inj' i j h := Fin.ext (by simpa using congrArg Fin.val h)

/-- Edges joining adjacent coordinates in the same block. -/
def uncuts (B : BlockShape n) : Finset (Fin (n - 1)) :=
  Finset.univ \ B.cuts

@[simp] theorem mem_uncuts_iff (B : BlockShape n) (i : Fin (n - 1)) :
    i ∈ B.uncuts ↔ i ∉ B.cuts := by
  simp [uncuts]

theorem mem_boundaries_iff (B : BlockShape n) (j : Fin (n + 1)) :
    j ∈ B.toComposition.boundaries ↔
      j = 0 ∨ j = Fin.last n ∨
        ∃ i ∈ B.cuts, interiorBoundary n i = j := by
  constructor
  · intro hj
    by_cases h0 : j = 0
    · exact Or.inl h0
    by_cases hn : j = Fin.last n
    · exact Or.inr (Or.inl hn)
    have hj0 : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using h0
    have hjn : j.val ≠ n := by simpa only [Fin.ext_iff, Fin.val_last] using hn
    let i : Fin (n - 1) := ⟨j.val - 1, by omega⟩
    have hi : interiorBoundary n i = j := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    refine Or.inr (Or.inr ⟨i, ?_, hi⟩)
    apply (B.mem_cuts_iff i).mpr
    change interiorBoundary n i ∈ B.toComposition.boundaries
    rwa [hi]
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · exact B.toComposition.toCompositionAsSet.zero_mem
    · exact B.toComposition.toCompositionAsSet.getLast_mem
    · exact (B.mem_cuts_iff i).mp hi

theorem boundaries_eq_insert_cuts (B : BlockShape n) :
    B.toComposition.boundaries =
      insert 0 (insert (Fin.last n) (B.cuts.map (interiorBoundary n))) := by
  ext j
  simp only [mem_boundaries_iff, Finset.mem_insert, Finset.mem_map]

theorem cuts_card (B : BlockShape n) :
    B.cuts.card = B.length - 1 := by
  by_cases hn : n = 0
  · subst n
    have hl : B.length = 0 := Nat.eq_zero_of_le_zero B.length_le
    have hc : B.cuts = ∅ := by
      ext i
      exact Fin.elim0 i
    simp [hc, hl]
  · have h0n : (0 : Fin (n + 1)) ≠ Fin.last n := by
      simpa only [Fin.ext_iff, Fin.val_zero, Fin.val_last, ne_eq, eq_comm] using hn
    have h0 : (0 : Fin (n + 1)) ∉ B.cuts.map (interiorBoundary n) := by
      simp only [Finset.mem_map, not_exists, not_and]
      intro i _ hi
      have : i.val + 1 = 0 := congrArg Fin.val hi
      omega
    have hlast : Fin.last n ∉ B.cuts.map (interiorBoundary n) := by
      simp only [Finset.mem_map, not_exists, not_and]
      intro i _ hi
      have : i.val + 1 = n := congrArg Fin.val hi
      omega
    have hc := B.toComposition.card_boundaries_eq_succ_length
    rw [B.boundaries_eq_insert_cuts, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_insert, h0n, h0, or_self, not_false_eq_true]),
      Finset.card_insert_of_notMem hlast, Finset.card_map] at hc
    have hl : B.toComposition.length = B.length := by
      simp only [toComposition, Composition.length, List.length_ofFn]
    omega

theorem uncuts_card (B : BlockShape n) :
    B.uncuts.card = n - B.length := by
  by_cases hn : n = 0
  · subst n
    have hl : B.length = 0 := Nat.eq_zero_of_le_zero B.length_le
    simp [uncuts, hl]
  · have hl : 0 < B.length := by
      by_contra h
      have hzero : B.length = 0 := by omega
      have he : IsEmpty (Fin B.length) := by rw [hzero]; infer_instance
      have hs := B.sum_eq
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
      exact hn hs.symm
    rw [uncuts, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, B.cuts_card]
    have := B.length_le
    omega

theorem sign_eq_pow_uncuts_card (B : BlockShape n) :
    (-1 : ℤ) ^ (n - B.length) = (-1 : ℤ) ^ B.uncuts.card := by
  rw [B.uncuts_card]

end Langlands.GeneralLinear.BlockShape
