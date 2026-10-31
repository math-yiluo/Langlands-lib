import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Classification.Segments
import Mathlib.Data.Finset.Sort

/-! Finite labels for minimal permutations whose target blocks remain whole. -/

noncomputable section

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric CuspidalSupport

section General

variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Each target block has all its inverse images in one source block. -/
def TargetBlocksContained : Prop :=
  ∀ a b, blockIndex C a = blockIndex C b →
    blockIndex B (w.symm a) = blockIndex B (w.symm b)

/-- The source label of the first coordinate of a target block. -/
def targetBlockLabel (i : Fin C.length) : Fin B.length :=
  blockIndex B (w.symm (C.index i ⟨0, C.positive i⟩))

theorem inverse_blockIndex_eq (hw : TargetBlocksContained B C w) (a : Fin n) :
    blockIndex B (w.symm a) = targetBlockLabel B C w (blockIndex C a) :=
  hw a (C.index (blockIndex C a) ⟨0, C.positive _⟩) (by rw [blockIndex_index])

/-- The image of a source block is the set of coordinates with its label. -/
theorem range_sourceBlock (hw : TargetBlocksContained B C w) (j : Fin B.length) :
    Set.range (fun a : Fin (B.size j) => w (B.index j a)) =
      {x | targetBlockLabel B C w (blockIndex C x) = j} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change targetBlockLabel B C w (blockIndex C (w (B.index j a))) = j
    rw [← inverse_blockIndex_eq B C w hw, Equiv.symm_apply_apply, blockIndex_index]
  · intro hx
    obtain ⟨a, ha⟩ := exists_index_of_blockIndex_eq B
      ((inverse_blockIndex_eq B C w hw x).trans hx)
    refine ⟨a, ?_⟩
    change w (B.index j a) = x
    rw [ha, Equiv.apply_symm_apply]

/-- Minimal permutations with whole target blocks are determined by their labels. -/
theorem eq_of_targetBlockLabel_eq {v : Equiv.Perm (Fin n)}
    (hw : IsMinimalRepresentative B C w) (hv : IsMinimalRepresentative B C v)
    (hcw : TargetBlocksContained B C w) (hcv : TargetBlocksContained B C v)
    (he : targetBlockLabel B C w = targetBlockLabel B C v) : w = v := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨j, a⟩, rfl⟩ := B.indexEquiv.surjective x
  have hr : Set.range (fun a : Fin (B.size j) => w (B.index j a)) =
      Set.range (fun a : Fin (B.size j) => v (B.index j a)) := by
    rw [range_sourceBlock B C w hcw, range_sourceBlock B C v hcv, he]
  exact congrFun ((hw.1 j).eq_of_range_eq (hv.1 j) hr) a

end General

section Uniform

variable {m r : ℕ} (hr : 0 < r) (B : BlockShape (m * r))

/-- The coordinates assigned to a source block by a target-block labeling. -/
abbrev labelCoordinates (lab : Fin m → Fin B.length) (j : Fin B.length) :=
  {x : Fin (m * r) // lab (blockIndex (BlockShape.uniform m r hr) x) = j}

/-- Coordinates with label `j` consist of one copy of `Fin r` per labeled block. -/
def labelCoordinateEquiv (lab : Fin m → Fin B.length) (j : Fin B.length) :
    labelCoordinates hr B lab j ≃ {i : Fin m // lab i = j} × Fin r where
  toFun x := ⟨⟨blockIndex (BlockShape.uniform m r hr) x.val, x.property⟩,
    ((BlockShape.uniform m r hr).indexEquiv.symm x.val).2⟩
  invFun y := ⟨(BlockShape.uniform m r hr).index y.1.val y.2, by
    exact (congrArg lab (blockIndex_index (BlockShape.uniform m r hr) y.1.val y.2)).trans
      y.1.property⟩
  left_inv x := Subtype.ext ((BlockShape.uniform m r hr).indexEquiv.apply_symm_apply x.val)
  right_inv y := by
    rcases y with ⟨⟨i, hi⟩, a⟩
    apply Prod.ext
    · apply Subtype.ext
      exact blockIndex_index (BlockShape.uniform m r hr) i a
    · exact congrArg (β := Fin r) (fun z : (BlockShape.uniform m r hr).Index => z.2)
        ((BlockShape.uniform m r hr).indexEquiv.symm_apply_apply ⟨i, a⟩)

theorem card_labelCoordinates (lab : Fin m → Fin B.length) (j : Fin B.length) :
    Nat.card (labelCoordinates hr B lab j) = Nat.card {i : Fin m // lab i = j} * r := by
  rw [Nat.card_congr (labelCoordinateEquiv hr B lab j), Nat.card_prod, Nat.card_fin]

/-- The cardinality constraint imposed by the source block sizes. -/
abbrev LabelAssignment : Type :=
  {lab : Fin m → Fin B.length //
    ∀ j, Nat.card {i : Fin m // lab i = j} * r = B.size j}

/-- The minimal permutations with whole uniform target blocks. -/
abbrev WholeTargetRepresentatives : Type :=
  {w : MinimalRepresentatives B (BlockShape.uniform m r hr) //
    TargetBlocksContained B (BlockShape.uniform m r hr) w.val}

theorem targetBlockLabel_card (w : WholeTargetRepresentatives hr B) (j : Fin B.length) :
    Nat.card {i : Fin m //
      targetBlockLabel B (BlockShape.uniform m r hr) w.val.val i = j} * r = B.size j := by
  let e : labelCoordinates hr B
      (targetBlockLabel B (BlockShape.uniform m r hr) w.val.val) j ≃
      {x : Fin (m * r) // blockIndex B x = j} :=
    w.val.val.symm.subtypeEquiv (fun x => by
      rw [inverse_blockIndex_eq B (BlockShape.uniform m r hr) w.val.val w.property x])
  exact (card_labelCoordinates hr B
    (fun i : Fin m => targetBlockLabel B (BlockShape.uniform m r hr) w.val.val i) j).symm.trans
      ((Nat.card_congr e).trans (TotalConjugatingCount.card_blockIndex_fiber B j))

/-- The increasing enumeration of the coordinates assigned to source block `j`. -/
def labelCoordinateOrderIso (lab : LabelAssignment B) (j : Fin B.length) :
    Fin (B.size j) ≃o labelCoordinates hr B lab.val j :=
  Fintype.orderIsoFinOfCardEq _ (by
    rw [← Nat.card_eq_fintype_card, card_labelCoordinates hr B, lab.property j])

/-- Partition all coordinates by the source label assigned to their target block. -/
def labelPartitionEquiv (lab : Fin m → Fin B.length) :
    ((j : Fin B.length) × labelCoordinates hr B lab j) ≃ Fin (m * r) where
  toFun x := x.2.val
  invFun x := ⟨lab (blockIndex (BlockShape.uniform m r hr) x), ⟨x, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨j, x, hx⟩
    dsimp
    cases hx
    rfl
  right_inv _ := rfl

/-- Send each source block increasingly onto all coordinates with its label. -/
def permutationFromLabels (lab : LabelAssignment B) : Equiv.Perm (Fin (m * r)) :=
  (B.indexEquiv.symm.trans
    (Equiv.sigmaCongrRight fun j => (labelCoordinateOrderIso hr B lab j).toEquiv)).trans
    (labelPartitionEquiv hr B lab.val)

theorem permutationFromLabels_index (lab : LabelAssignment B) (j : Fin B.length)
    (a : Fin (B.size j)) :
    permutationFromLabels hr B lab (B.index j a) =
      (labelCoordinateOrderIso hr B lab j a).val := by
  change (labelPartitionEquiv hr B lab.val)
    ((Equiv.sigmaCongrRight fun j => (labelCoordinateOrderIso hr B lab j).toEquiv)
      (B.indexEquiv.symm (B.indexEquiv ⟨j, a⟩))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem permutationFromLabels_source_strictMono (lab : LabelAssignment B)
    (j : Fin B.length) :
    StrictMono (fun a : Fin (B.size j) => permutationFromLabels hr B lab (B.index j a)) := by
  intro a b hab
  change permutationFromLabels hr B lab (B.index j a) <
    permutationFromLabels hr B lab (B.index j b)
  rw [permutationFromLabels_index hr B lab j a, permutationFromLabels_index hr B lab j b]
  exact (labelCoordinateOrderIso hr B lab j).strictMono hab

theorem permutationFromLabels_inverse_label (lab : LabelAssignment B)
    (x : Fin (m * r)) :
    blockIndex B ((permutationFromLabels hr B lab).symm x) =
      lab.val (blockIndex (BlockShape.uniform m r hr) x) := by
  obtain ⟨⟨j, a⟩, ha⟩ := B.indexEquiv.surjective ((permutationFromLabels hr B lab).symm x)
  have hx : permutationFromLabels hr B lab (B.index j a) = x :=
    (congrArg (permutationFromLabels hr B lab) ha).trans
      ((permutationFromLabels hr B lab).apply_symm_apply x)
  rw [← ha]
  change blockIndex B (B.index j a) = lab.val (blockIndex (BlockShape.uniform m r hr) x)
  rw [blockIndex_index]
  have hl := (labelCoordinateOrderIso hr B lab j a).property
  rw [← permutationFromLabels_index, hx] at hl
  exact hl.symm

theorem permutationFromLabels_contained (lab : LabelAssignment B) :
    TargetBlocksContained B (BlockShape.uniform m r hr) (permutationFromLabels hr B lab) := by
  intro a b hab
  rw [permutationFromLabels_inverse_label, permutationFromLabels_inverse_label, hab]

theorem permutationFromLabels_minimal (lab : LabelAssignment B) :
    IsMinimalRepresentative B (BlockShape.uniform m r hr) (permutationFromLabels hr B lab) := by
  refine ⟨permutationFromLabels_source_strictMono hr B lab, ?_⟩
  intro i a b hab
  let j := lab.val i
  have hlabel (c : Fin r) :
      blockIndex B ((permutationFromLabels hr B lab).symm
        ((BlockShape.uniform m r hr).index i c)) = j := by
    exact (permutationFromLabels_inverse_label hr B lab _).trans
      (congrArg lab.val (blockIndex_index (BlockShape.uniform m r hr) i c))
  obtain ⟨x, hx⟩ := exists_index_of_blockIndex_eq B (hlabel a)
  obtain ⟨y, hy⟩ := exists_index_of_blockIndex_eq B (hlabel b)
  have hxy : x < y := by
    apply (permutationFromLabels_source_strictMono hr B lab j).lt_iff_lt.mp
    rw [hx, hy, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact index_strictMono (BlockShape.uniform m r hr) i hab
  change (permutationFromLabels hr B lab).symm ((BlockShape.uniform m r hr).index i a) <
    (permutationFromLabels hr B lab).symm ((BlockShape.uniform m r hr).index i b)
  rw [← hx, ← hy]
  exact index_strictMono B j hxy

theorem targetBlockLabel_permutationFromLabels (lab : LabelAssignment B) :
    targetBlockLabel B (BlockShape.uniform m r hr) (permutationFromLabels hr B lab) =
      lab.val := by
  funext i
  exact (permutationFromLabels_inverse_label hr B lab _).trans
    (congrArg lab.val (blockIndex_index (BlockShape.uniform m r hr) i _))

/-- Exact finite parametrization by target-block labels with the required sizes. -/
def wholeTargetEquivLabels :
    WholeTargetRepresentatives hr B ≃ LabelAssignment B where
  toFun w := ⟨targetBlockLabel B (BlockShape.uniform m r hr) w.val.val,
    targetBlockLabel_card hr B w⟩
  invFun lab := ⟨⟨permutationFromLabels hr B lab,
    permutationFromLabels_minimal hr B lab⟩, permutationFromLabels_contained hr B lab⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact eq_of_targetBlockLabel_eq B (BlockShape.uniform m r hr) _
      (permutationFromLabels_minimal hr B _) w.val.property
      (permutationFromLabels_contained hr B _) w.property
      (targetBlockLabel_permutationFromLabels hr B _)
  right_inv lab := Subtype.ext (targetBlockLabel_permutationFromLabels hr B lab)

end Uniform

end Langlands.Classification.ShuffleRefinement
