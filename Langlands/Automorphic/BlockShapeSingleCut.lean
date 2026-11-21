import Langlands.Automorphic.BlockShapeLeviSliceFactors
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Geometric.BlockWeylCutProof

/-! # Refining exactly one ordered block by one additional cut -/

noncomputable section

universe u

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear

variable {n : ℕ} (B : BlockShape n)

private theorem blockIndex_val (i : Fin B.length) (a : Fin (B.size i)) :
    (B.index i a).val = (∑ j : Fin i.val, B.size (Fin.castLE i.isLt.le j)) + a.val := by
  change (Fin.cast B.sum_eq (finSigmaFinEquiv ⟨i, a⟩)).val = _
  rw [Fin.val_cast, finSigmaFinEquiv_apply]

/-- The global cut after local position `c` inside block `i`. -/
def blockShapeSingleCut (i : Fin B.length) (c : Fin (B.size i - 1)) : Fin (n - 1) :=
  ⟨(B.index i ⟨c.val, by have := c.isLt; omega⟩).val, by
    let b : Fin (B.size i) := ⟨c.val + 1, by have := c.isLt; omega⟩
    have hb := (B.index i b).isLt
    rw [blockIndex_val] at hb ⊢
    change _ + (c.val + 1) < n at hb
    change _ + c.val < n - 1
    omega⟩

theorem blockShapeSingleCut_notMem (i : Fin B.length) (c : Fin (B.size i - 1)) :
    blockShapeSingleCut B i c ∉ B.cuts := by
  let a : Fin (B.size i) := ⟨c.val, by have := c.isLt; omega⟩
  let b : Fin (B.size i) := ⟨c.val + 1, by have := c.isLt; omega⟩
  have hb : (B.index i b).val = (B.index i a).val + 1 := by
    rw [blockIndex_val, blockIndex_val]
    exact (Nat.add_assoc _ _ _).symm
  intro hc
  have h := (Geometric.blockIndex_eq_iff_cut_sides B (B.index i a) (B.index i b)).mp (by
    rw [Geometric.blockIndex_index, Geometric.blockIndex_index])
  have hle := (h (blockShapeSingleCut B i c) hc).mp
    (show (B.index i a).val ≤ (B.index i a).val from le_rfl)
  change (B.index i b).val ≤ (B.index i a).val at hle
  omega

theorem cuts_ssubset_insert_blockShapeSingleCut (i : Fin B.length) (c : Fin (B.size i - 1)) :
    B.cuts ⊂ insert (blockShapeSingleCut B i c) B.cuts :=
  Finset.ssubset_insert (blockShapeSingleCut_notMem B i c)

/-- The local two-block weights for a cut inside a block. -/
def oneCutWeight {d : ℕ} (c : Fin (d - 1)) (a : Fin d) : ℤ :=
  if a.val ≤ c.val then 1 else 0

private theorem standardBlockWeight_insert {s : Finset (Fin (n - 1))}
    {c : Fin (n - 1)} (hc : c ∉ s) (x : Fin n) :
    standardBlockWeight (insert c s) x =
      standardBlockWeight s x - if c.val < x.val then 1 else 0 := by
  unfold standardBlockWeight
  rw [Finset.filter_insert]
  split_ifs with hx
  · rw [Finset.card_insert_of_notMem (fun h => hc (Finset.mem_filter.mp h).1)]
    push_cast
    omega
  · omega

private theorem singleCutWeight_compare (i : Fin B.length) (c : Fin (B.size i - 1))
    (a b : Fin (B.size i)) :
    standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index i a) ≤
      standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index i b) ↔
    oneCutWeight c a ≤ oneCutWeight c b := by
  have h (x : Fin (B.size i)) :
      (blockShapeSingleCut B i c).val < (B.index i x).val ↔ c.val < x.val := by
    change (B.index i ⟨c.val, _⟩).val < (B.index i x).val ↔ c.val < x.val
    rw [blockIndex_val, blockIndex_val]
    exact Nat.add_lt_add_iff_left
  let hcut := blockShapeSingleCut_notMem B i c
  simp only [standardBlockWeight_insert hcut, h, standardBlockWeight_on_index, oneCutWeight]
  split_ifs <;> omega

private theorem singleCutWeight_le_of_ne (i j : Fin B.length) (hij : j ≠ i)
    (c : Fin (B.size i - 1)) (a b : Fin (B.size j)) :
    standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index j a) ≤
      standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index j b) := by
  let z : Fin (B.size i) := ⟨c.val, by have := c.isLt; omega⟩
  let hcut := blockShapeSingleCut_notMem B i c
  rw [standardBlockWeight_insert hcut, standardBlockWeight_insert hcut,
    standardBlockWeight_on_index, standardBlockWeight_on_index]
  change -(j.val : ℤ) - (if (B.index i z).val < (B.index j a).val then 1 else 0) ≤
    -(j.val : ℤ) - (if (B.index i z).val < (B.index j b).val then 1 else 0)
  rcases hij.lt_or_gt with hj | hj
  · have ha : ¬ (B.index i z).val < (B.index j a).val :=
      (B.index_lt_index_of_block_lt hj a z).not_gt
    have hb : ¬ (B.index i z).val < (B.index j b).val :=
      (B.index_lt_index_of_block_lt hj b z).not_gt
    simp only [ite_eq_right ha, ite_eq_right hb, le_rfl]
  · have ha : (B.index i z).val < (B.index j a).val := B.index_lt_index_of_block_lt hj z a
    have hb : (B.index i z).val < (B.index j b).val := B.index_lt_index_of_block_lt hj z b
    simp only [ite_eq_left ha, ite_eq_left hb, le_rfl]

variable (A : Type u) [CommRing A]

/-- The genuine inclusion of a single block group into the ordered block
diagonal matrices of the ambient general linear group. -/
def blockShapeSingleEmbedding (i : Fin B.length) :
    GeneralLinear (B.size i) A →* GeneralLinear n A :=
  (B.leviEmbedding A).comp (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) A) i)

/-- The unipotent complement inside the original Levi after inserting an
internal cut is the embedded two-block radical of that one block. -/
theorem blockUnipotent_inf_levi_insert_singleCut (i : Fin B.length) (c : Fin (B.size i - 1)) :
    blockUnipotentSubgroup A (standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts)) ⊓
      blockLeviSubgroup A (standardBlockWeight B.cuts) =
      (blockUnipotentSubgroup A (oneCutWeight c)).map (blockShapeSingleEmbedding B A i) := by
  classical
  apply Subgroup.ext
  intro g
  rw [Subgroup.mem_inf, standardBlockWeight_eq_blockShapeWeight B, blockLeviSubgroup_blockShapeWeight]
  have hdiag (j : Fin B.length) (a b : Fin (B.size j)) :
      (1 : Matrix (Fin n) (Fin n) A) (B.index j a) (B.index j b) =
        (1 : Matrix (Fin (B.size j)) (Fin (B.size j)) A) a b := by
    simp only [Matrix.one_apply, (B.index j).injective.eq_iff]
  constructor
  · rintro ⟨hu, ⟨m, rfl⟩⟩
    have hentry (j : Fin B.length) (a b : Fin (B.size j)) (hw :
        standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index j a) ≤
          standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts) (B.index j b)) :
        m j a b = (1 : Matrix (Fin (B.size j)) (Fin (B.size j)) A) a b := by
      have h := hu (B.index j a) (B.index j b) hw
      rwa [B.leviEmbedding_apply_same, hdiag] at h
    refine ⟨m i, fun a b hw => hentry i a b ((singleCutWeight_compare B i c a b).mpr hw), ?_⟩
    apply congrArg (B.leviEmbedding A)
    funext j
    change (Pi.mulSingle i (m i) : B.Levi A) j = m j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj]
      symm
      apply Units.ext
      ext a b
      exact hentry j a b (singleCutWeight_le_of_ne B i j hj c a b)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨?_, ⟨Pi.mulSingle i v, rfl⟩⟩
    intro x y hxy
    obtain ⟨j, a, rfl⟩ := exists_eq_index B x
    obtain ⟨k, b, rfl⟩ := exists_eq_index B y
    change B.leviEmbedding A (Pi.mulSingle i v) (B.index j a) (B.index k b) = _
    by_cases hjk : j = k
    · subst k
      rw [B.leviEmbedding_apply_same, hdiag]
      by_cases hj : j = i
      · subst j
        rw [Pi.mulSingle_eq_same]
        exact hv a b ((singleCutWeight_compare B i c a b).mp hxy)
      · rw [Pi.mulSingle_eq_of_ne hj]
        rfl
    · rw [B.leviEmbedding_apply_ne A _ a b hjk]
      exact (Matrix.one_apply_ne (fun he => hjk (congrArg Sigma.fst
        ((index_eq_index_iff B a b).mp he)))).symm

end Langlands.Automorphic
