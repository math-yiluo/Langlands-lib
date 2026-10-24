import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.RefinementCoordinates

/-! The first block and remaining blocks in their actual consecutive coordinates. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Geometric

universe u
variable {n k : ℕ} (B : BlockShape n) (h : B.length = k + 2)

/-- Original label of the first block. -/
def headIndex : Fin B.length := Fin.cast h.symm 0

/-- Original label of a block in the tail, preserving its order. -/
def tailIndex (i : Fin (k + 1)) : Fin B.length := Fin.cast h.symm i.succ

/-- Rank of the first block. -/
def headRank : ℕ := B.size (B.headIndex h)

/-- Rank of all blocks after the first. -/
def tailRank : ℕ := ∑ i : Fin (k + 1), B.size (B.tailIndex h i)

theorem headRank_pos : 0 < B.headRank h := B.positive _

theorem tailRank_pos : 0 < B.tailRank h := by
  apply Finset.sum_pos
  · intro i _
    exact B.positive _
  · exact Finset.univ_nonempty

theorem headRank_add_tailRank : B.headRank h + B.tailRank h = n := by
  calc
    _ = ∑ i : Fin (k + 2), B.size (Fin.cast h.symm i) := (Fin.sum_univ_succ _).symm
    _ = ∑ i, B.size i := Equiv.sum_comp (finCongr h.symm) _
    _ = n := B.sum_eq

/-- The remaining ordered positive blocks, with their actual total rank. -/
def tailShape : BlockShape (B.tailRank h) where
  length := k + 1
  size := fun i => B.size (B.tailIndex h i)
  positive := fun _ => B.positive _
  sum_eq := rfl

/-- The first block considered as a one-block shape. -/
def headShape : BlockShape (B.headRank h) where
  length := 1
  size := fun _ => B.headRank h
  positive := fun _ => B.headRank_pos h
  sum_eq := by simp

/-- The two outer blocks: the first block and the full tail. -/
def headTailShape : BlockShape n :=
  (show BlockShape (B.headRank h + B.tailRank h) from
    { length := 2
      size := Fin.cases (B.headRank h) (fun _ => B.tailRank h)
      positive := by intro i; refine Fin.cases (B.headRank_pos h) (fun _ => B.tailRank_pos h) i
      sum_eq := by simp [Fin.sum_univ_succ] }).rankCast (B.headRank_add_tailRank h)

@[simp] theorem tailShape_length : (B.tailShape h).length = k + 1 := rfl
@[simp] theorem tailShape_size (i : Fin (k + 1)) :
    (B.tailShape h).size i = B.size (B.tailIndex h i) := rfl
@[simp] theorem headShape_length : (B.headShape h).length = 1 := rfl
@[simp] theorem headShape_size (i : Fin 1) : (B.headShape h).size i = B.headRank h := rfl
@[simp] theorem headTailShape_length : (B.headTailShape h).length = 2 := rfl
@[simp] theorem headTailShape_size_zero : (B.headTailShape h).size (0 : Fin 2) = B.headRank h := rfl
@[simp] theorem headTailShape_size_one : (B.headTailShape h).size (1 : Fin 2) = B.tailRank h := rfl

/-- Refining the first outer block trivially, and the second by the original tail. -/
def headTailRefinement :
    (i : Fin 2) → BlockShape (Fin.cases (B.headRank h) (fun _ => B.tailRank h) i) :=
  Fin.cases (B.headShape h) (fun _ => B.tailShape h)

@[simp] theorem headTailRefinement_zero : B.headTailRefinement h (0 : Fin 2) = B.headShape h := rfl
@[simp] theorem headTailRefinement_one : B.headTailRefinement h (1 : Fin 2) = B.tailShape h := rfl

/-- The nested labels, in consecutive order, are exactly the original labels. -/
def headTailBlockEquiv :
    ((i : Fin 2) × Fin (B.headTailRefinement h i).length) ≃
      Fin B.length :=
  finSigmaFinEquiv.trans (finCongr (by
    rw [Fin.sum_univ_two]
    simp only [headTailRefinement_zero, headTailRefinement_one, headShape_length, tailShape_length]
    omega))

@[simp] theorem headTailBlockEquiv_head (j : Fin 1) :
    B.headTailBlockEquiv h ⟨(0 : Fin 2), j⟩ = B.headIndex h := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  apply Fin.ext
  simp [headTailBlockEquiv, headIndex, Equiv.trans_apply, finCongr_apply, finSigmaFinEquiv_apply]

@[simp] theorem headTailBlockEquiv_tail (j : Fin (k + 1)) :
    B.headTailBlockEquiv h ⟨(1 : Fin 2), j⟩ = B.tailIndex h j := by
  apply Fin.ext
  simp [headTailBlockEquiv, tailIndex, Equiv.trans_apply, finCongr_apply,
    finSigmaFinEquiv_apply, Nat.add_comm]

/-- Flattening preserves every original block size. -/
theorem headTailBlock_size (a : (i : Fin 2) ×
    Fin (B.headTailRefinement h i).length) :
    (B.headTailRefinement h a.1).size a.2 = B.size (B.headTailBlockEquiv h a) := by
  rcases a with ⟨i, j⟩
  fin_cases i
  · change B.headRank h = B.size (B.headTailBlockEquiv h ⟨(0 : Fin 2), (j : Fin 1)⟩)
    exact congrArg B.size (B.headTailBlockEquiv_head h j).symm
  · change B.size (B.tailIndex h j) =
      B.size (B.headTailBlockEquiv h ⟨(1 : Fin 2), (j : Fin (k + 1))⟩)
    exact congrArg B.size (B.headTailBlockEquiv_tail h j).symm

/-- The first block starts at coordinate zero. -/
theorem head_index_val (x : Fin (B.headRank h)) :
    (B.index (B.headIndex h) x).val = x.val := by
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp [headIndex]

/-- The tail keeps its consecutive coordinates, shifted by the first rank. -/
theorem tail_index_val (j : Fin (k + 1)) (x : Fin ((B.tailShape h).size j)) :
    (B.index (B.tailIndex h j) x).val =
      B.headRank h + ((B.tailShape h).index j x).val := by
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  change (∑ a : Fin (j.val + 1), B.size (Fin.castLE (B.tailIndex h j).isLt.le a)) +
    x.val = B.headRank h +
      ((∑ a : Fin j.val, (B.tailShape h).size (Fin.castLE j.isLt.le a)) + x.val)
  rw [Fin.sum_univ_succ, ← Nat.add_assoc]
  congr 1

/-- The head outer block starts at zero. -/
theorem headTailShape_index_zero (x : Fin (B.headRank h)) :
    ((B.headTailShape h).index (0 : Fin 2) x).val = x.val := by
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp

/-- The tail outer block starts at the first block's rank. -/
theorem headTailShape_index_one (x : Fin (B.tailRank h)) :
    ((B.headTailShape h).index (1 : Fin 2) x).val = B.headRank h + x.val := by
  simp only [index, indexEquiv, Function.Embedding.coeFn_mk, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp

private theorem index_val_congr {i j : Fin B.length} (hij : i = j)
    (x : Fin (B.size i)) (y : Fin (B.size j)) (hxy : x.val = y.val) :
    (B.index i x).val = (B.index j y).val := by
  subst j
  have he : x = y := Fin.ext hxy
  subst y
  rfl

/-- Each nested standard coordinate is exactly its original standard coordinate. -/
theorem headTail_index (i : Fin 2) (j : Fin (B.headTailRefinement h i).length)
    (x : Fin ((B.headTailRefinement h i).size j)) :
    (B.headTailShape h).index i ((B.headTailRefinement h i).index j x) =
      B.index (B.headTailBlockEquiv h ⟨i, j⟩)
        (Fin.cast (B.headTailBlock_size h ⟨i, j⟩) x) := by
  fin_cases i
  · apply Fin.ext
    exact ((B.headTailShape_index_zero h _).trans
      ((B.headShape h).singleBlock_index_val rfl j x)).trans
        ((B.index_val_congr (B.headTailBlockEquiv_head h j) _ x rfl).trans
          (B.head_index_val h x)).symm
  · apply Fin.ext
    exact (B.headTailShape_index_one h _).trans
      ((B.index_val_congr (B.headTailBlockEquiv_tail h j) _ x rfl).trans
        (B.tail_index_val h j x)).symm

/-- The tail rank is the ambient rank minus the first rank. -/
theorem tailRank_eq_sub : B.tailRank h = n - B.headRank h := by
  have := B.headRank_add_tailRank h
  omega

/-- The total number of flattened blocks is the original length. -/
theorem headTailRefinement_total_length :
    (∑ i : Fin 2, (B.headTailRefinement h i).length) = B.length := by
  rw [Fin.sum_univ_two]
  change 1 + (k + 1) = B.length
  omega

/-- The total of the flattened ordered sizes is the original rank. -/
theorem headTailRefinement_total_rank :
    (∑ i : Fin 2, ∑ j, (B.headTailRefinement h i).size j) = n := by
  simp_rw [BlockShape.sum_eq]
  change (∑ i : Fin 2, (B.headTailShape h).size i) = n
  exact (B.headTailShape h).sum_eq

/-- Tail labels have exactly their original order. -/
theorem tailIndex_strictMono : StrictMono (B.tailIndex h) := by
  intro i j hij
  change i.val + 1 < j.val + 1
  exact Nat.add_lt_add_right hij 1

/-- The first label precedes every label in the tail. -/
theorem headIndex_lt_tailIndex (j : Fin (k + 1)) : B.headIndex h < B.tailIndex h j := by
  change 0 < j.val + 1
  omega

/-- Nested block labels in distinct outer blocks preserve order. -/
theorem headTailBlock_lt_of_outer_lt {i j : Fin 2}
    (a : Fin (B.headTailRefinement h i).length)
    (b : Fin (B.headTailRefinement h j).length) (hij : i < j) :
    B.headTailBlockEquiv h ⟨i, a⟩ < B.headTailBlockEquiv h ⟨j, b⟩ :=
  B.refinementBlock_lt_of_outer_lt (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) (B.headTail_index h) a b hij

/-- Nested labels within each outer block preserve order. -/
theorem headTailBlock_strictMono (i : Fin 2) :
    StrictMono (fun j : Fin (B.headTailRefinement h i).length =>
      B.headTailBlockEquiv h ⟨i, j⟩) :=
  B.refinementBlock_strictMono (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) (B.headTail_index h) i

variable (R : Type u) [CommRing R]

/-- Regroup the original Levi into its head and tail nested products. -/
def headTailNestedLeviEquiv : B.Levi R ≃* ∀ i : Fin 2, (B.headTailRefinement h i).Levi R :=
  B.nestedLeviEquiv (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R

/-- The actual first/tail refined Levi, using the published nested-subgroup map. -/
def headTailLeviEquiv : B.Levi R ≃*
    refinedLevi R (B.headTailShape h) (B.headTailRefinement h) :=
  B.leviRefinementEquiv (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R

@[simp] theorem headTailNestedLeviEquiv_entry (m : B.Levi R) (i : Fin 2)
    (j : Fin (B.headTailRefinement h i).length)
    (x y : Fin ((B.headTailRefinement h i).size j)) :
    B.headTailNestedLeviEquiv h R m i j x y =
      m (B.headTailBlockEquiv h ⟨i, j⟩)
        (Fin.cast (B.headTailBlock_size h ⟨i, j⟩) x)
        (Fin.cast (B.headTailBlock_size h ⟨i, j⟩) y) := rfl

set_option maxHeartbeats 800000 in
/-- The reverse regrouping has the opposite size cast. -/
theorem headTailNestedLeviEquiv_symm_apply
    (m : ∀ i : Fin 2, (B.headTailRefinement h i).Levi R) (i : Fin 2)
    (j : Fin (B.headTailRefinement h i).length) :
    (B.headTailNestedLeviEquiv h R).symm m (B.headTailBlockEquiv h ⟨i, j⟩) =
      reindex (R := R) (finCongr (B.headTailBlock_size h ⟨i, j⟩)) (m i j) :=
  B.nestedLeviEquiv_symm_apply (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R m i j

@[simp] theorem headTailLeviEquiv_val (m : B.Levi R) (i : Fin 2) :
    (B.headTailLeviEquiv h R m).val i =
      (B.headTailRefinement h i).leviEmbedding R (B.headTailNestedLeviEquiv h R m i) := rfl

/-- The nested embedding is exactly the original ambient block diagonal matrix. -/
theorem headTailLeviEquiv_embedding (m : B.Levi R) :
    (B.headTailShape h).leviEmbedding R (B.headTailLeviEquiv h R m).val =
      B.leviEmbedding R m :=
  B.leviEmbedding_leviRefinementEquiv (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R (B.headTail_index h) m

/-- The composed upper parabolic is the original actual subgroup. -/
theorem headTail_composedParabolic_eq :
    Parabolic.composedParabolic R (B.headTailShape h) (B.headTailRefinement h) =
      B.parabolic R :=
  B.composedParabolic_eq_of_coordinates (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R (B.headTail_index h)

/-- Identify the two parabolic subtype presentations, retaining each matrix. -/
def headTailParabolicEquiv : B.parabolic R ≃*
    Parabolic.composedParabolic R (B.headTailShape h) (B.headTailRefinement h) :=
  B.parabolicRefinementEquiv (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R (B.headTail_index h)

@[simp] theorem headTailParabolicEquiv_val (g : B.parabolic R) :
    (B.headTailParabolicEquiv h R g).val = g.val := rfl

/-- The composed diagonal projection agrees with the original projection. -/
theorem headTail_composedLeviProjection (g : B.parabolic R) :
    Parabolic.composedLeviProjection R (B.headTailShape h) (B.headTailRefinement h)
      (B.headTailParabolicEquiv h R g) = B.headTailLeviEquiv h R (B.leviProjection R g) :=
  B.composedLeviProjection_parabolicRefinementEquiv (B.headTailShape h)
    (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h) R
      (B.headTail_index h) g

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- Regrouping respects the topologies on the actual Levi products. -/
def headTailNestedLeviEquivContinuous :
    B.Levi R ≃ₜ* ∀ i : Fin 2, (B.headTailRefinement h i).Levi R :=
  B.nestedLeviEquivContinuous (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R

/-- The actual refined Levi equivalence is continuous in both directions. -/
def headTailLeviEquivContinuous : B.Levi R ≃ₜ*
    refinedLevi R (B.headTailShape h) (B.headTailRefinement h) :=
  B.leviRefinementEquivContinuous (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R

/-- Parabolic identification is continuous in both directions. -/
def headTailParabolicEquivContinuous : B.parabolic R ≃ₜ*
    Parabolic.composedParabolic R (B.headTailShape h) (B.headTailRefinement h) :=
  B.parabolicRefinementEquivContinuous (B.headTailShape h) (B.headTailRefinement h)
    (B.headTailBlockEquiv h) (B.headTailBlock_size h) R (B.headTail_index h)

end Topology
end Langlands.GeneralLinear.BlockShape
