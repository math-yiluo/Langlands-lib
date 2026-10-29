import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Classification.Segments

/-!
# Block combinatorics of an adjacent merge

Let `Γ` merge blocks `k` and `k + 1` of a block shape `B`. For a permutation `w`
whose source-Levi intersection `Γ ∩ w⁻¹(B)` is a standard refinement `S` of `Γ`,
this module shows:

* a block shape is determined by its "same block" relation on coordinates;
* the refinement `S` records exactly which coordinates of each block of `Γ`
  are sent by `w` into a common block of `B`;
* if `w` conjugates the Levi of `B` onto itself, then `S` is the adjacent
  refinement of `Γ`;
* if no two blocks of `B` fit together into one block of `B` and every
  component of `S` is trivial or adjacent, then `w` conjugates the Levi of `B`
  onto itself; so otherwise some component of `S` is proper and not adjacent;
* the minimal `(Γ, B)` representatives conjugating the Levi of `B` onto itself
  are the minimal `(B, B)` conjugating permutations that are minimal for `Γ`.
-/

namespace Langlands.Classification.SegmentEdge

open GeneralLinear Geometric CuspidalSupport

variable {n : ℕ}

section Shapes

/-- Monotone labels compare as the order of coordinates, up to equal labels. -/
theorem blockIndex_le_iff (D : BlockShape n) (a b : Fin n) :
    blockIndex D a ≤ blockIndex D b ↔ a ≤ b ∨ blockIndex D a = blockIndex D b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact Or.inl hab
    · exact Or.inr (le_antisymm h (blockIndex_monotone D (le_of_not_ge hab)))
  · rintro (h | h)
    · exact blockIndex_monotone D h
    · exact h.le

/-- A block shape is determined by the relation "same block" on coordinates. -/
theorem eq_of_sameBlock {D D' : BlockShape n}
    (h : ∀ a b, blockIndex D a = blockIndex D b ↔ blockIndex D' a = blockIndex D' b) :
    D = D' := by
  have hle : ∀ a b, blockIndex D a ≤ blockIndex D b ↔ blockIndex D' a ≤ blockIndex D' b := by
    intro a b
    rw [blockIndex_le_iff, blockIndex_le_iff, h]
  let φ : Fin D.length → Fin D'.length := fun i => blockIndex D' (D.index i ⟨0, D.positive i⟩)
  have hφ : ∀ a, blockIndex D' a = φ (blockIndex D a) := by
    intro a
    exact (h _ _).mp (by rw [blockIndex_index])
  have hmono : StrictMono φ := by
    intro i i' hii
    have h1 : ¬ blockIndex D (D.index i' ⟨0, D.positive i'⟩) ≤
        blockIndex D (D.index i ⟨0, D.positive i⟩) := by
      rw [blockIndex_index, blockIndex_index]
      exact not_le.mpr hii
    rw [hle] at h1
    exact lt_of_not_ge h1
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨blockIndex D (D'.index c ⟨0, D'.positive c⟩), ?_⟩
    rw [← hφ, blockIndex_index]
  have hl : D.length = D'.length := by
    simpa only [Fintype.card_fin] using
      Fintype.card_of_bijective ⟨hmono.injective, hsurj⟩
  have hcast : ∀ i, φ i = Fin.cast hl i := by
    intro i
    let ψ : Fin D.length → Fin D.length := fun i => Fin.cast hl.symm (φ i)
    have hψ : StrictMono ψ := fun x y hxy => by
      change (φ x : ℕ) < (φ y : ℕ)
      exact hmono hxy
    have := congrFun hψ.eq_id i
    apply Fin.ext
    simpa [ψ] using congrArg Fin.val this
  apply BlockShape.ext_of_size hl
  intro i
  rw [← TotalConjugatingCount.card_blockIndex_fiber D i,
    ← TotalConjugatingCount.card_blockIndex_fiber D' (Fin.cast hl i)]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun a => ?_
  rw [hφ, hcast]
  constructor
  · rintro rfl
    rfl
  · intro he
    exact Fin.cast_injective hl he

end Shapes

section Adjacent

variable (B : BlockShape n) (k : ℕ) (hk : k + 1 < B.length)

/-- The original block of a coordinate of a merged block. -/
theorem blockIndex_merge_index (j : Fin (B.adjacentMerge k hk).length)
    (a : Fin ((B.adjacentMerge k hk).size j)) :
    blockIndex B ((B.adjacentMerge k hk).index j a) =
      B.adjacentBlockEquiv k hk ⟨j, blockIndex (B.adjacentRefinement k hk j) a⟩ := by
  obtain ⟨⟨t, x⟩, rfl⟩ := (B.adjacentRefinement k hk j).indexEquiv.surjective a
  change blockIndex B ((B.adjacentMerge k hk).index j ((B.adjacentRefinement k hk j).index t x)) =
    B.adjacentBlockEquiv k hk ⟨j, blockIndex (B.adjacentRefinement k hk j)
      ((B.adjacentRefinement k hk j).index t x)⟩
  rw [BlockShape.adjacent_index, blockIndex_index, blockIndex_index]

/-- Inside one merged block, two coordinates lie in the same original block exactly
when they lie in the same block of the adjacent refinement. -/
theorem sameBlock_merge_iff (j : Fin (B.adjacentMerge k hk).length)
    (a b : Fin ((B.adjacentMerge k hk).size j)) :
    blockIndex B ((B.adjacentMerge k hk).index j a) =
        blockIndex B ((B.adjacentMerge k hk).index j b) ↔
      blockIndex (B.adjacentRefinement k hk j) a =
        blockIndex (B.adjacentRefinement k hk j) b := by
  rw [blockIndex_merge_index, blockIndex_merge_index, (B.adjacentBlockEquiv k hk).apply_eq_iff_eq,
    Sigma.mk.inj_iff]
  exact ⟨fun h => eq_of_heq h.2, fun h => ⟨rfl, heq_of_eq h⟩⟩

/-- Original blocks lie inside merged blocks. -/
theorem mergeBlock_eq_of_blockIndex_eq {a b : Fin n} (h : blockIndex B a = blockIndex B b) :
    blockIndex (B.adjacentMerge k hk) a = blockIndex (B.adjacentMerge k hk) b := by
  rw [BlockShape.blockIndex_adjacentMerge, BlockShape.blockIndex_adjacentMerge, h]

/-- A permutation minimal for the merged and original shapes is minimal for the
original shape on both sides. -/
theorem isMinimalRepresentative_of_merge {w : Equiv.Perm (Fin n)}
    (hw : IsMinimalRepresentative (B.adjacentMerge k hk) B w) :
    IsMinimalRepresentative B B w := by
  rw [CuspidalSupport.isMinimalRepresentative_iff] at hw ⊢
  exact ⟨fun a b hab hlt => hw.1 a b (mergeBlock_eq_of_blockIndex_eq B k hk hab) hlt, hw.2⟩

end Adjacent

section Intersections

variable {F : Type*} [Field F]

/-- A one-block test element: the transposition matrix of `a, b` in block `j` and
the identity in the other blocks. Its entries between coordinates of different
labels vanish exactly when `a` and `b` have the same label. -/
theorem mulSingle_swap_entries_iff (D : BlockShape n) {α : Fin D.length → Type*}
    (lab : ∀ i, Fin (D.size i) → α i) (j : Fin D.length) (a b : Fin (D.size j)) :
    (∀ i x y, lab i x ≠ lab i y →
        (Pi.mulSingle j (permutation (D.size j) F (Equiv.swap a b)) : D.Levi F) i x y = 0) ↔
      lab j a = lab j b := by
  constructor
  · intro H
    have := H j
    simp only [Pi.mulSingle_eq_same] at this
    exact (TotalConjugatingCount.swap_entries_vanish_iff (R := F) (lab j) id
      Function.injective_id a b).mp this
  · intro hab i x y hxy
    by_cases hij : i = j
    · subst hij
      simp only [Pi.mulSingle_eq_same]
      exact (TotalConjugatingCount.swap_entries_vanish_iff (R := F) (lab i) id
        Function.injective_id a b).mpr hab x y hxy
    · rw [Pi.mulSingle_eq_of_ne hij]
      have hxy' : x ≠ y := fun e => hxy (e ▸ rfl)
      simp [Matrix.one_apply_ne hxy']

/-- If the source-Levi intersection of `w` is the standard refinement `S`, then
`S` records exactly which coordinates of each block are sent into one target block. -/
theorem sameBlock_of_sourceLevi_eq (D C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement D) (hS : sourceLevi F D C w = refinedLevi F D S)
    (j : Fin D.length) (a b : Fin (D.size j)) :
    blockIndex (S j) a = blockIndex (S j) b ↔
      blockIndex C (w (D.index j a)) = blockIndex C (w (D.index j b)) := by
  classical
  let g : D.Levi F := Pi.mulSingle j (permutation (D.size j) F (Equiv.swap a b))
  have key := SetLike.ext_iff.mp hS g
  rw [mem_sourceLevi_iff, mem_refinedLevi] at key
  simp only [levi_mem_iff] at key
  rw [← mulSingle_swap_entries_iff (F := F) D (fun i x => blockIndex (S i) x) j a b,
    ← mulSingle_swap_entries_iff (F := F) D (fun i x => blockIndex C (w (D.index i x))) j a b]
  exact key.symm

end Intersections

section Conjugation

variable {F : Type*} [Field F] (B : BlockShape n) (k : ℕ) (hk : k + 1 < B.length)

/-- If every component of the source-Levi refinement is trivial or adjacent,
then `w` sends each block of `B` into a single block of `B`. -/
theorem blockIndex_apply_eq_of_trivial_or_adjacent (w : Equiv.Perm (Fin n))
    (S : BlockRefinement (B.adjacentMerge k hk))
    (hS : sourceLevi F (B.adjacentMerge k hk) B w = refinedLevi F (B.adjacentMerge k hk) S)
    (h : ∀ j, (S j).length ≤ 1 ∨ S j = B.adjacentRefinement k hk j)
    {x y : Fin n} (hxy : blockIndex B x = blockIndex B y) :
    blockIndex B (w x) = blockIndex B (w y) := by
  obtain ⟨⟨j, a⟩, rfl⟩ := (B.adjacentMerge k hk).indexEquiv.surjective x
  obtain ⟨⟨j', b⟩, rfl⟩ := (B.adjacentMerge k hk).indexEquiv.surjective y
  change blockIndex B ((B.adjacentMerge k hk).index j a) =
    blockIndex B ((B.adjacentMerge k hk).index j' b) at hxy
  change blockIndex B (w ((B.adjacentMerge k hk).index j a)) =
    blockIndex B (w ((B.adjacentMerge k hk).index j' b))
  have hj : j = j' := by
    have := mergeBlock_eq_of_blockIndex_eq B k hk hxy
    rwa [blockIndex_index, blockIndex_index] at this
  subst hj
  apply (sameBlock_of_sourceLevi_eq (B.adjacentMerge k hk) B w S hS j a b).mp
  rcases h j with hl | he
  · apply Fin.ext
    have h1 := (blockIndex (S j) a).isLt
    have h2 := (blockIndex (S j) b).isLt
    omega
  · rw [he]
    exact (sameBlock_merge_iff B k hk j a b).mp hxy

/-- If no two blocks of `B` fit together into one block of `B`, and every
component of the source-Levi refinement of `w` is trivial or adjacent, then `w`
conjugates the Levi of `B` onto itself. -/
theorem conjugatesLevi_of_trivial_or_adjacent
    (hsize : ∀ c c' d : Fin B.length, c ≠ c' → B.size d < B.size c + B.size c')
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement (B.adjacentMerge k hk))
    (hS : sourceLevi F (B.adjacentMerge k hk) B w = refinedLevi F (B.adjacentMerge k hk) S)
    (h : ∀ j, (S j).length ≤ 1 ∨ S j = B.adjacentRefinement k hk j) :
    ConjugatesLevi (F := F) B B w := by
  have hfwd := fun {x y : Fin n} (hxy : blockIndex B x = blockIndex B y) =>
    blockIndex_apply_eq_of_trivial_or_adjacent (F := F) B k hk w S hS h hxy
  let d : Fin B.length → Fin B.length := fun c =>
    blockIndex B (w (B.index c ⟨0, B.positive c⟩))
  have hd : ∀ x, blockIndex B (w x) = d (blockIndex B x) := fun x =>
    hfwd (by rw [blockIndex_index])
  have hinj : Function.Injective d := by
    intro c c' hcc
    by_contra hne
    let f : {x : Fin n // blockIndex B x = c} ⊕ {x : Fin n // blockIndex B x = c'} →
        {y : Fin n // blockIndex B y = d c} :=
      Sum.elim (fun x => ⟨w x.val, by rw [hd, x.property]⟩)
        (fun x => ⟨w x.val, by rw [hd, x.property, hcc]⟩)
    have hf : Function.Injective f := by
      rintro (x | x) (y | y) hxy <;>
        have hv := w.injective (congrArg Subtype.val hxy)
      · exact congrArg Sum.inl (Subtype.ext hv)
      · exact absurd (x.property.symm.trans ((congrArg (blockIndex B) hv).trans y.property)) hne
      · exact absurd (y.property.symm.trans
          ((congrArg (blockIndex B) hv.symm).trans x.property)) hne
      · exact congrArg Sum.inr (Subtype.ext hv)
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum, TotalConjugatingCount.card_blockIndex_fiber,
      TotalConjugatingCount.card_blockIndex_fiber,
      TotalConjugatingCount.card_blockIndex_fiber] at hcard
    exact absurd hcard (not_le.mpr (hsize c c' (d c) hne))
  rw [TotalConjugatingCount.conjugatesLevi_iff]
  intro a b
  rw [hd, hd]
  exact hinj.eq_iff.symm

/-- If `w` conjugates the Levi of `B` onto itself, its source-Levi
refinement of the merged shape is the adjacent refinement. -/
theorem eq_adjacentRefinement_of_conjugatesLevi (w : Equiv.Perm (Fin n))
    (S : BlockRefinement (B.adjacentMerge k hk))
    (hS : sourceLevi F (B.adjacentMerge k hk) B w = refinedLevi F (B.adjacentMerge k hk) S)
    (hw : ConjugatesLevi (F := F) B B w) :
    S = B.adjacentRefinement k hk := by
  funext j
  apply eq_of_sameBlock
  intro a b
  rw [sameBlock_of_sourceLevi_eq (B.adjacentMerge k hk) B w S hS j a b,
    ← (TotalConjugatingCount.conjugatesLevi_iff (F := F) B B w).mp hw,
    sameBlock_merge_iff]

/-- A permutation not conjugating the Levi of `B` onto itself has a block
whose source-Levi refinement is proper (at least two blocks) and differs from
the adjacent refinement. -/
theorem exists_bad_block_of_not_conjugatesLevi
    (hsize : ∀ c c' d : Fin B.length, c ≠ c' → B.size d < B.size c + B.size c')
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement (B.adjacentMerge k hk))
    (hS : sourceLevi F (B.adjacentMerge k hk) B w = refinedLevi F (B.adjacentMerge k hk) S)
    (hw : ¬ ConjugatesLevi (F := F) B B w) :
    ∃ j, 1 < (S j).length ∧ S j ≠ B.adjacentRefinement k hk j := by
  by_contra hne
  push Not at hne
  apply hw
  refine conjugatesLevi_of_trivial_or_adjacent B k hk hsize w S hS fun j => ?_
  by_cases hl : 1 < (S j).length
  · exact Or.inr (hne j hl)
  · exact Or.inl (not_lt.mp hl)

/-- Minimal `(merged, B)` representatives conjugating the Levi of `B` onto
itself are the minimal `(B, B)` conjugating permutations that are minimal for
the merged shape. -/
def retainedEquiv :
    {w : MinimalRepresentatives (B.adjacentMerge k hk) B //
        ConjugatesLevi (F := F) B B w.val} ≃
      {v : MinimalConjugatingPermutations (F := F) B B //
        IsMinimalRepresentative (B.adjacentMerge k hk) B v.val.val} where
  toFun w := ⟨⟨⟨w.val.val, isMinimalRepresentative_of_merge B k hk w.val.property⟩,
    w.property⟩, w.val.property⟩
  invFun v := ⟨⟨v.val.val.val, v.property⟩, v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The uniform shape satisfies the size condition of C5 and C7. -/
theorem uniform_size_lt (m r : ℕ) (hr : 0 < r)
    (c c' d : Fin (BlockShape.uniform m r hr).length) (_ : c ≠ c') :
    (BlockShape.uniform m r hr).size d <
      (BlockShape.uniform m r hr).size c + (BlockShape.uniform m r hr).size c' := by
  change r < r + r
  omega

end Conjugation

end Langlands.Classification.SegmentEdge
