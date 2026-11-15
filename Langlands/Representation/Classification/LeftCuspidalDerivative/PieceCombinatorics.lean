import Langlands.Representation.Classification.LeftCuspidalDerivative.PieceTransport
import Langlands.Representation.Geometric.IntersectionLeviModulusBalance
import Langlands.Representation.Geometric.FlattenedIntersectionTransport
import Langlands.Representation.CuspidalSupport.LeviSplitContraction
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Group.GL.SingleBlock

/-!
# Combinatorics of the inner blocks of a geometric piece

Let `w` be a minimal representative for the block shapes `B` and `C` of `GL_n`, with
intersection refinements `S` of `B` and `R` of `C`. The flattened refinements are conjugate
under `w`, and their block bijection sends each inner block of `S` to an inner block of `R`.
For an inner block `q` of `R` we write `sourceBlock hw q` for the inner block of `S` sent
to it. This file proves:

* every inner block of `S` sent into the first block of `C` is the first inner block of its
  block of `B`;
* in each block of `C`, the inner blocks come in increasing order of their source inner
  blocks; in the first block of `C` their source blocks of `B` strictly increase;
* the number of inner blocks of a block of `B` is at most the number of blocks of `C`;
* if `C` has two blocks and its first block is a single inner block coming from the first
  block of `B`, then `w` is the identity.
-/

noncomputable section

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport

universe uF

section Coordinates

variable {n : ℕ}

/-- A coordinate in a block numbered zero is its position in the block. -/
theorem index_val_of_val_eq_zero (B : BlockShape n) (i : Fin B.length) (hi : (i : ℕ) = 0)
    (b : Fin (B.size i)) : ((B.index i b : Fin n) : ℕ) = b := by
  rw [LeviAdmissibility.index_val]
  have h0 : ∑ k : Fin i, B.size (Fin.castLE i.2.le k) = 0 :=
    Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  omega

/-- The first inner block of the first block is the flattened block numbered zero. -/
theorem flattenBlockEquiv_val_eq_zero (B : BlockShape n) (S : BlockRefinement B)
    (q : (i : Fin B.length) × Fin (S i).length) (h₁ : (q.1 : ℕ) = 0) (h₂ : (q.2 : ℕ) = 0) :
    (B.flattenBlockEquiv S q : ℕ) = 0 := by
  change (finSigmaFinEquiv q : ℕ) = 0
  rw [finSigmaFinEquiv_apply]
  have h0 : ∑ k : Fin q.1, (S (Fin.castLE q.1.2.le k)).length = 0 :=
    Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  omega

/-- The block of a coordinate is the outer block of its flattened block. -/
theorem blockIndex_eq_fst_flatten (C : BlockShape n) (R : BlockRefinement C) (x : Fin n) :
    blockIndex C x = ((C.flattenBlockEquiv R).symm (blockIndex (C.flatten R) x)).1 := by
  obtain ⟨⟨k, c⟩, rfl⟩ := (C.flatten R).indexEquiv.surjective x
  change blockIndex C ((C.flatten R).index k c) =
    ((C.flattenBlockEquiv R).symm (blockIndex (C.flatten R) ((C.flatten R).index k c))).1
  rw [blockIndex_index, C.flatten_index R k c, blockIndex_index]

end Coordinates

section Source

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
  {S : BlockRefinement B} {R : BlockRefinement C}

/-- The inner block of `S` that the block bijection of the flattened conjugation sends to the
inner block `q` of `R`. -/
def sourceBlock (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (q : (j : Fin C.length) × Fin (R j).length) : (i : Fin B.length) × Fin (S i).length :=
  (B.flattenBlockEquiv S).symm ((blockEquiv hw).symm (C.flattenBlockEquiv R q))

theorem flattenBlockEquiv_sourceBlock
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (q : (j : Fin C.length) × Fin (R j).length) :
    B.flattenBlockEquiv S (sourceBlock hw q) = (blockEquiv hw).symm (C.flattenBlockEquiv R q) :=
  (B.flattenBlockEquiv S).apply_symm_apply _

/-- The inverse image of a coordinate lies in the flattened source block corresponding to its
flattened target block. -/
theorem blockIndex_flatten_symm_apply
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (k' : Fin (C.flatten R).length) (x : Fin n) (hx : blockIndex (C.flatten R) x = k') :
    blockIndex (B.flatten S) (w.symm x) = (blockEquiv hw).symm k' := by
  rw [Equiv.eq_symm_apply]
  change blockMap (B.flatten S) (C.flatten R) w (blockIndex (B.flatten S) (w.symm x)) = k'
  rw [← blockIndex_apply_eq_blockMap hw, Equiv.apply_symm_apply, hx]

/-- The coordinates of the source inner block of `q` are sent into the block `q.1` of `C`. -/
theorem blockIndex_apply_sourceBlock
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (q : (j : Fin C.length) × Fin (R j).length)
    (c : Fin ((S (sourceBlock hw q).1).size (sourceBlock hw q).2)) :
    blockIndex C (w (B.index (sourceBlock hw q).1
      ((S (sourceBlock hw q).1).index (sourceBlock hw q).2 c))) = q.1 := by
  let k := (blockEquiv hw).symm (C.flattenBlockEquiv R q)
  have hx : B.index (sourceBlock hw q).1 ((S (sourceBlock hw q).1).index (sourceBlock hw q).2 c) =
      (B.flatten S).index k c :=
    (B.flatten_index S k c).symm
  rw [hx, blockIndex_eq_fst_flatten C R, blockIndex_apply_eq_blockMap hw]
  have hb : blockIndex (B.flatten S) ((B.flatten S).index k c) = k := blockIndex_index _ _ _
  rw [hb]
  change ((C.flattenBlockEquiv R).symm (blockEquiv hw k)).1 = q.1
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The source inner block of `q` has the size of `q`. -/
theorem size_sourceBlock (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (q : (j : Fin C.length) × Fin (R j).length) :
    (S (sourceBlock hw q).1).size (sourceBlock hw q).2 = (R q.1).size q.2 := by
  have h := size_blockEquiv_symm hw (C.flattenBlockEquiv R q)
  rw [C.flatten_size_flattenBlockEquiv R q] at h
  exact h

/-- An inner block of `S` whose coordinates are sent into the first block of `C` is the first
inner block of its block. -/
theorem val_eq_zero_of_blockIndex_eq (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S) (i : Fin B.length) (j : Fin (S i).length)
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0)
    (h : ∀ c, blockIndex C (w (B.index i ((S i).index j c))) = j₀) : (j : ℕ) = 0 := by
  by_contra hj
  have hpos := (S i).positive j
  have hlen : 0 < (S i).length := by omega
  have hpos0 := (S i).positive ⟨0, hlen⟩
  have hlt : blockIndex (S i) ((S i).index ⟨0, hlen⟩ ⟨0, hpos0⟩) <
      blockIndex (S i) ((S i).index j ⟨0, hpos⟩) := by
    rw [blockIndex_index, blockIndex_index, Fin.lt_def]
    change 0 < (j : ℕ)
    omega
  have h' := (refinement_lt_iff_of_sourceLevi F B C w hmin.1 S hS i _ _).mp hlt
  rw [h ⟨0, hpos⟩, Fin.lt_def, hj₀] at h'
  omega

/-- The source inner block of an inner block of the first block of `C` is a first inner
block. -/
theorem sourceBlock_snd_eq_zero (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (q : (j : Fin C.length) × Fin (R j).length) (hq : (q.1 : ℕ) = 0) :
    ((sourceBlock hw q).2 : ℕ) = 0 :=
  val_eq_zero_of_blockIndex_eq hmin hS _ _ q.1 hq (blockIndex_apply_sourceBlock hw q)

/-- Inside one block of `C`, the inner blocks come in increasing order of their flattened
source blocks. -/
theorem sourceIndex_strictMono (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w) (j₀ : Fin C.length) :
    StrictMono (fun l : Fin (R j₀).length =>
      (blockEquiv hw).symm (C.flattenBlockEquiv R ⟨j₀, l⟩)) := by
  intro l l' hll
  have hpos := (R j₀).positive l
  have hpos' := (R j₀).positive l'
  have hxy : w.symm (C.index j₀ ((R j₀).index l ⟨0, hpos⟩)) <
      w.symm (C.index j₀ ((R j₀).index l' ⟨0, hpos'⟩)) :=
    hmin.2 j₀ (((R j₀).index_lt_iff _ _).mpr (Or.inl hll))
  have hx := blockIndex_flatten_symm_apply hw (C.flattenBlockEquiv R ⟨j₀, l⟩)
    (C.index j₀ ((R j₀).index l ⟨0, hpos⟩))
    ((congrArg (blockIndex (C.flatten R)) (C.index_index_eq_flatten R ⟨j₀, l⟩ ⟨0, hpos⟩)).trans
      (blockIndex_index _ _ _))
  have hy := blockIndex_flatten_symm_apply hw (C.flattenBlockEquiv R ⟨j₀, l'⟩)
    (C.index j₀ ((R j₀).index l' ⟨0, hpos'⟩))
    ((congrArg (blockIndex (C.flatten R)) (C.index_index_eq_flatten R ⟨j₀, l'⟩ ⟨0, hpos'⟩)).trans
      (blockIndex_index _ _ _))
  have hle := blockIndex_monotone (B.flatten S) hxy.le
  rw [hx, hy] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  have hq := (C.flattenBlockEquiv R).injective ((blockEquiv hw).symm.injective heq)
  have hl : l = l' := by
    rw [Sigma.mk.inj_iff] at hq
    exact eq_of_heq hq.2
  exact absurd hl (ne_of_lt hll)

/-- In the first block of `C`, the source blocks of `B` of the inner blocks strictly
increase. -/
theorem sourceBlock_fst_strictMono (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0) :
    StrictMono (fun l : Fin (R j₀).length => (sourceBlock hw ⟨j₀, l⟩).1) := by
  intro l l' hll
  have h := sourceIndex_strictMono hmin hw j₀ hll
  have h' : B.flattenBlockEquiv S (sourceBlock hw ⟨j₀, l⟩) <
      B.flattenBlockEquiv S (sourceBlock hw ⟨j₀, l'⟩) := by
    rw [flattenBlockEquiv_sourceBlock, flattenBlockEquiv_sourceBlock]
    exact h
  rcases (B.flattenBlockEquiv_lt_iff S _ _).mp h' with h1 | ⟨_, h2⟩
  · exact h1
  · have e₁ := sourceBlock_snd_eq_zero hmin hS hw ⟨j₀, l⟩ hj₀
    have e₂ := sourceBlock_snd_eq_zero hmin hS hw ⟨j₀, l'⟩ hj₀
    omega

/-- The first block of `C` has at most as many inner blocks as `B` has blocks. -/
theorem length_le_of_sourceBlock (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0) : (R j₀).length ≤ B.length := by
  simpa using Fintype.card_le_of_injective _
    (sourceBlock_fst_strictMono hmin hS hw j₀ hj₀).injective

/-- If `B` has two blocks and the first block of `C` has two inner blocks, these come from
the two blocks of `B` in order. -/
theorem sourceBlock_fst_val_of_length_two (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (hB : B.length = 2) (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0) (hl : (R j₀).length = 2)
    (l : Fin (R j₀).length) : ((sourceBlock hw ⟨j₀, l⟩).1 : ℕ) = l := by
  have hmono := sourceBlock_fst_strictMono hmin hS hw j₀ hj₀
  have h01 := hmono (show (⟨0, by omega⟩ : Fin (R j₀).length) < ⟨1, by omega⟩ from
    Fin.lt_def.mpr (by simp))
  rw [Fin.lt_def] at h01
  dsimp only at h01
  have h1 := (sourceBlock hw ⟨j₀, ⟨1, by omega⟩⟩).1.isLt
  rcases l with ⟨l, hl'⟩
  have hl2 : l = 0 ∨ l = 1 := by omega
  rcases hl2 with rfl | rfl
  · change ((sourceBlock hw ⟨j₀, ⟨0, by omega⟩⟩).1 : ℕ) = 0
    omega
  · change ((sourceBlock hw ⟨j₀, ⟨1, by omega⟩⟩).1 : ℕ) = 1
    omega

/-- A block of `B` has at most as many inner blocks as `C` has blocks. -/
theorem refinement_length_le (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S) (i : Fin B.length) :
    (S i).length ≤ C.length := by
  let f : Fin (S i).length → Fin C.length := fun j =>
    blockIndex C (w (B.index i ((S i).index j ⟨0, (S i).positive j⟩)))
  have hf : StrictMono f := by
    intro j j' hjj
    refine (refinement_lt_iff_of_sourceLevi F B C w hmin.1 S hS i _ _).mp ?_
    rw [blockIndex_index, blockIndex_index]
    exact hjj
  simpa using Fintype.card_le_of_injective f hf.injective

/-- If `C` has two blocks and its first block is a single inner block coming from the first
block of `B`, then the minimal representative is the identity. -/
theorem eq_one_of_sourceBlock (hmin : IsMinimalRepresentative B C w)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hw : ConjugatesLevi (F := F) (B.flatten S) (C.flatten R) w)
    (hC : C.length = 2) (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0) (hl : (R j₀).length = 1)
    (hsrc : ((sourceBlock hw ⟨j₀, ⟨0, by omega⟩⟩).1 : ℕ) = 0) : w = 1 := by
  let q : (j : Fin C.length) × Fin (R j).length := ⟨j₀, ⟨0, by omega⟩⟩
  let k' := C.flattenBlockEquiv R q
  let k := (blockEquiv hw).symm k'
  have hk' : (k' : ℕ) = 0 := flattenBlockEquiv_val_eq_zero C R q hj₀ rfl
  have hk : (k : ℕ) = 0 := by
    have h := flattenBlockEquiv_val_eq_zero B S (sourceBlock hw q) hsrc
      (sourceBlock_snd_eq_zero hmin hS hw q hj₀)
    rw [flattenBlockEquiv_sourceBlock] at h
    exact h
  have hmin' := isMinimalRepresentative_flatten S R hmin
  -- The coordinates of the flattened block `k` are fixed.
  have hfix : ∀ c : Fin ((B.flatten S).size k),
      w ((B.flatten S).index k c) = (B.flatten S).index k c := by
    intro c
    apply Fin.ext
    have hm : (blockMap (B.flatten S) (C.flatten R) w k : ℕ) = 0 := by
      change (blockEquiv hw k : ℕ) = 0
      rw [Equiv.apply_symm_apply]
      exact hk'
    rw [apply_index_eq hmin' hw k c, index_val_of_val_eq_zero _ _ hm,
      index_val_of_val_eq_zero _ _ hk]
    rfl
  have hsize : (B.flatten S).size k = C.size j₀ := by
    rw [size_blockEquiv_symm hw k', C.flatten_size_flattenBlockEquiv R q]
    exact (R j₀).singleBlock_size hl _
  -- `w` fixes the first block of `C`.
  have hlow : ∀ x : Fin n, (x : ℕ) < C.size j₀ → w x = x := by
    intro x hx
    have hx' : (x : ℕ) < (B.flatten S).size k := hsize ▸ hx
    have h := hfix ⟨x, hx'⟩
    have hxe : (B.flatten S).index k ⟨x, hx'⟩ = x :=
      Fin.ext (index_val_of_val_eq_zero _ _ hk _)
    rwa [hxe] at h
  have hlow' : ∀ x : Fin n, (x : ℕ) < C.size j₀ → w.symm x = x := by
    intro x hx
    have h := w.symm_apply_apply x
    rwa [hlow x hx] at h
  -- The remaining coordinates form the second block of `C`.
  let j₁ : Fin C.length := ⟨1, by omega⟩
  have hhigh : ∀ x : Fin n, C.size j₀ ≤ (x : ℕ) → blockIndex C x = j₁ := by
    intro x hx
    obtain ⟨β, hβ⟩ := exists_index_of_blockIndex_eq C (rfl : blockIndex C x = blockIndex C x)
    by_contra hne
    have hv : (blockIndex C x : ℕ) = 0 := by
      have h2 := (blockIndex C x).isLt
      have h3 : (blockIndex C x : ℕ) ≠ 1 := fun h => hne (Fin.ext h)
      omega
    have h4 := index_val_of_val_eq_zero C (blockIndex C x) hv β
    rw [hβ] at h4
    have hj : blockIndex C x = j₀ := Fin.ext (hv.trans hj₀.symm)
    have h5 : C.size (blockIndex C x) = C.size j₀ := congrArg C.size hj
    have h6 := β.isLt
    omega
  have hhigh' : ∀ y : Fin n, C.size j₀ ≤ (y : ℕ) → C.size j₀ ≤ (w.symm y : ℕ) := by
    intro y hy
    by_contra h
    push Not at h
    have h' := hlow (w.symm y) h
    rw [Equiv.apply_symm_apply] at h'
    rw [← h'] at h
    omega
  have hmono : StrictMono w.symm := by
    intro x y hxy
    by_cases hy : (y : ℕ) < C.size j₀
    · have hx : (x : ℕ) < C.size j₀ := lt_trans (Fin.lt_def.mp hxy) hy
      rw [hlow' x hx, hlow' y hy]
      exact hxy
    by_cases hx : (x : ℕ) < C.size j₀
    · push Not at hy
      rw [hlow' x hx, Fin.lt_def]
      exact lt_of_lt_of_le hx (hhigh' y hy)
    push Not at hx hy
    obtain ⟨α, rfl⟩ := exists_index_of_blockIndex_eq C (hhigh x hx)
    obtain ⟨β, rfl⟩ := exists_index_of_blockIndex_eq C (hhigh y hy)
    exact hmin.2 j₁ ((index_strictMono C j₁).lt_iff_lt.mp hxy)
  have hid : ∀ x, w.symm x = x := fun x => le_antisymm hmono.apply_le hmono.le_apply
  refine Equiv.ext fun x => ?_
  have h := hid (w x)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

end Source

end Langlands.Classification.LeftCuspidalDerivative
