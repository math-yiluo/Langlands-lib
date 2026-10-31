import Langlands.Representation.Classification.SegmentEdgeCombinatorics
import Langlands.Group.GL.SingleBlock

/-!
# Uniform target blocks and divisible source refinements

These are finite block-coordinate facts for the shuffle Jacquet calculation.
They assume the source-Levi intersection is the specified standard refinement;
no geometric-lemma or representation-theoretic proposition is assumed.
-/

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric CuspidalSupport

variable {K : Type*} [Field K]

section General

variable {n : ℕ}
variable (B C : BlockShape n) (w : Equiv.Perm (Fin n))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B C w = refinedLevi K B S)

/-- The image of a block of the source refinement lies in the target block
containing the image of its first coordinate. -/
def sourceBlockEmbedding (j : Fin B.length) (i : Fin (S j).length) :
    Fin ((S j).size i) ↪
      {x : Fin n // blockIndex C x =
        blockIndex C (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))} where
  toFun a := ⟨w (B.index j ((S j).index i a)), by
    apply (SegmentEdge.sameBlock_of_sourceLevi_eq B C w S hS j _ _).mp
    simp only [blockIndex_index]⟩
  inj' := by
    intro a b hab
    exact (S j).index i |>.injective
      ((B.index j).injective (w.injective (congrArg Subtype.val hab)))

include hS in
/-- A source refinement block cannot exceed its containing target block. -/
theorem source_size_le_target (j : Fin B.length) (i : Fin (S j).length) :
    (S j).size i ≤
      C.size (blockIndex C (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))) := by
  have h := Nat.card_le_card_of_injective
    (sourceBlockEmbedding B C w S hS j i)
    (sourceBlockEmbedding B C w S hS j i).injective
  simpa only [Nat.card_fin, TotalConjugatingCount.card_blockIndex_fiber] using h

end General

section Uniform

variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform m r hr) w = refinedLevi K B S)

include hr hS

/-- A positive multiple of the uniform target rank that fits in one target block
is that rank itself. -/
theorem source_size_eq_of_dvd
    (j : Fin B.length) (i : Fin (S j).length) (hi : r ∣ (S j).size i) :
    (S j).size i = r := by
  apply le_antisymm
  · exact source_size_le_target B (BlockShape.uniform m r hr) w S hS j i
  · exact Nat.le_of_dvd ((S j).positive i) hi

/-- If all source refinement sizes are divisible by the uniform target rank,
the refinement of a block of size `q * r` has exactly `q` blocks. -/
theorem source_length_of_dvd
    (j : Fin B.length) (q : ℕ) (hq : B.size j = q * r)
    (hdiv : ∀ i, r ∣ (S j).size i) :
    (S j).length = q := by
  have hsize : ∀ i, (S j).size i = r :=
    fun i => source_size_eq_of_dvd hr B w S hS j i (hdiv i)
  have hsum : (S j).length * r = q * r := by
    calc
      (S j).length * r = ∑ i : Fin (S j).length, (S j).size i := by simp [hsize]
      _ = B.size j := (S j).sum_eq
      _ = q * r := hq
  nlinarith

/-- Such a source refinement is the uniform shape after transporting its total
rank by the supplied equality. -/
theorem source_eq_uniform_of_dvd
    (j : Fin B.length) (q : ℕ) (hq : B.size j = q * r)
    (hdiv : ∀ i, r ∣ (S j).size i) :
    (S j).rankCast hq = BlockShape.uniform q r hr := by
  apply BlockShape.ext_of_size (source_length_of_dvd hr B w S hS j q hq hdiv)
  intro i
  exact source_size_eq_of_dvd hr B w S hS j i (hdiv i)

/-- When its size is `r`, a source refinement block maps onto the whole
containing target block. -/
theorem sourceBlockEmbedding_surjective
    (j : Fin B.length) (i : Fin (S j).length) (hi : r ∣ (S j).size i) :
    Function.Surjective
      (sourceBlockEmbedding B (BlockShape.uniform m r hr) w S hS j i) := by
  have hinj := (sourceBlockEmbedding B (BlockShape.uniform m r hr) w S hS j i).injective
  have hcard :
      Nat.card {x : Fin (m * r) // blockIndex (BlockShape.uniform m r hr) x =
        blockIndex (BlockShape.uniform m r hr)
          (w (B.index j ((S j).index i ⟨0, (S j).positive i⟩)))} ≤
        Nat.card (Fin ((S j).size i)) := by
    rw [TotalConjugatingCount.card_blockIndex_fiber, Nat.card_fin]
    change r ≤ (S j).size i
    exact (source_size_eq_of_dvd hr B w S hS j i hi).ge
  exact (hinj.bijective_of_nat_card_le hcard).surjective

/-- A target block comes entirely from a single original source block if all
source refinement sizes are divisible by `r`. -/
theorem inverse_same_source_block
    (hdiv : ∀ j i, r ∣ (S j).size i)
    (a b : Fin (m * r))
    (hab : blockIndex (BlockShape.uniform m r hr) a =
      blockIndex (BlockShape.uniform m r hr) b) :
    blockIndex B (w.symm a) = blockIndex B (w.symm b) := by
  obtain ⟨⟨j, x⟩, hx⟩ := B.indexEquiv.surjective (w.symm a)
  obtain ⟨⟨i, y⟩, hy⟩ := (S j).indexEquiv.surjective x
  have ha : w (B.index j ((S j).index i y)) = a :=
    (congrArg w ((congrArg (B.index j) hy).trans hx)).trans (w.apply_symm_apply a)
  have halabel := (sourceBlockEmbedding B (BlockShape.uniform m r hr) w S hS j i y).property
  change blockIndex (BlockShape.uniform m r hr) (w (B.index j ((S j).index i y))) = _ at halabel
  rw [ha] at halabel
  obtain ⟨z, hz⟩ := sourceBlockEmbedding_surjective hr B w S hS j i (hdiv j i)
    ⟨b, hab.symm.trans halabel⟩
  have hb : w (B.index j ((S j).index i z)) = b := congrArg Subtype.val hz
  rw [← ha, ← hb, w.symm_apply_apply, w.symm_apply_apply,
    blockIndex_index, blockIndex_index]

/-- The reverse source-Levi intersection is full: every uniform target block
lies in one source block. -/
theorem reverse_sourceLevi_eq_top (hdiv : ∀ j i, r ∣ (S j).size i) :
    sourceLevi K (BlockShape.uniform m r hr) B w.symm = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_sourceLevi_iff]
  intro i a b hab
  exact (hab (inverse_same_source_block hr B w S hS hdiv _ _ (by
    simp only [blockIndex_index]))).elim

end Uniform

end Langlands.Classification.ShuffleRefinement
