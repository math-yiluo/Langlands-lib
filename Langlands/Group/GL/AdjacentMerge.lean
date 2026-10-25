import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Group.GL.RefinementCoordinates

/-! Actual Levi and parabolic comparisons for an adjacent merge and its swap. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Geometric

universe u
variable {n : ℕ} (B : BlockShape n) (j : ℕ) (h : j + 1 < B.length)
    (R : Type u) [CommRing R]

/-- The original Levi as the actual refined subgroup of the common merged Levi. -/
def adjacentLeviEquiv :
    B.Levi R ≃* refinedLevi R (B.adjacentMerge j h) (B.adjacentRefinement j h) :=
  leviRefinementEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R

/-- The inner block-diagonal description of each outer component. -/
@[simp] theorem adjacentLeviEquiv_val (m : B.Levi R)
    (i : Fin (B.adjacentMerge j h).length) :
    (B.adjacentLeviEquiv j h R m).val i =
      (B.adjacentRefinement j h i).leviEmbedding R
        (nestedLeviEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R m i) := rfl

/-- Reading an inner matrix entry recovers the corresponding original block entry. -/
@[simp] theorem adjacentLeviEquiv_entry (m : B.Levi R)
    (i : Fin (B.adjacentMerge j h).length) (k : Fin (B.adjacentRefinement j h i).length)
    (x y : Fin ((B.adjacentRefinement j h i).size k)) :
    ((refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentRefinement j h)).symm
      (B.adjacentLeviEquiv j h R m)) i k x y =
        m (B.adjacentBlockEquiv j h ⟨i, k⟩)
          (Fin.cast (B.adjacentBlock_size j h ⟨i, k⟩) x)
          (Fin.cast (B.adjacentBlock_size j h ⟨i, k⟩) y) := by
  change ((refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentRefinement j h)).symm
    (refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentRefinement j h)
      (nestedLeviEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R m))) i k x y = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The two descriptions give the same actual ambient matrix. -/
theorem adjacentLeviEmbedding (m : B.Levi R) :
    (B.adjacentMerge j h).leviEmbedding R (B.adjacentLeviEquiv j h R m).val =
      B.leviEmbedding R m :=
  leviEmbedding_leviRefinementEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R (B.adjacent_index j h) m

/-- The inner and outer triangularity conditions recover the actual standard parabolic. -/
theorem adjacentComposedParabolic_eq :
    Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentRefinement j h) = B.parabolic R :=
  composedParabolic_eq_of_coordinates B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R (B.adjacent_index j h)

/-- The parabolic identification retains the underlying ambient matrix. -/
def adjacentParabolicEquiv :
    B.parabolic R ≃* Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentRefinement j h) :=
  parabolicRefinementEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R (B.adjacent_index j h)

@[simp] theorem adjacentParabolicEquiv_val (g : B.parabolic R) :
    (B.adjacentParabolicEquiv j h R g).val = g.val := rfl

/-- Composed diagonal projection agrees with the original diagonal projection. -/
theorem adjacentComposedLeviProjection (g : B.parabolic R) :
    Parabolic.composedLeviProjection R (B.adjacentMerge j h) (B.adjacentRefinement j h)
      (B.adjacentParabolicEquiv j h R g) =
        B.adjacentLeviEquiv j h R (B.leviProjection R g) :=
  composedLeviProjection_parabolicRefinementEquiv B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R (B.adjacent_index j h) g

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The adjacent Levi identification is continuous in both directions. -/
def adjacentLeviEquivContinuous :
    B.Levi R ≃ₜ* refinedLevi R (B.adjacentMerge j h) (B.adjacentRefinement j h) :=
  leviRefinementEquivContinuous B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R

@[simp] theorem adjacentLeviEquivContinuous_toMulEquiv :
    (B.adjacentLeviEquivContinuous j h R).toMulEquiv =
      B.adjacentLeviEquiv j h R := rfl

/-- The matrix-preserving parabolic identification is continuous in both directions. -/
def adjacentParabolicEquivContinuous :
    B.parabolic R ≃ₜ* Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentRefinement j h) :=
  parabolicRefinementEquivContinuous B (B.adjacentMerge j h) (B.adjacentRefinement j h)
    (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h) R (B.adjacent_index j h)

@[simp] theorem adjacentParabolicEquivContinuous_toMulEquiv :
    (B.adjacentParabolicEquivContinuous j h R).toMulEquiv =
      B.adjacentParabolicEquiv j h R := rfl

end Topology

/-- The swapped Levi as the actual refined subgroup of the common merged Levi. -/
def adjacentSwapLeviEquiv :
    (B.permute (B.adjacentSwap j h)).Levi R ≃* refinedLevi R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h) :=
  leviRefinementEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R

/-- The inner block-diagonal description of each outer component. -/
@[simp] theorem adjacentSwapLeviEquiv_val (m : (B.permute (B.adjacentSwap j h)).Levi R)
    (i : Fin (B.adjacentMerge j h).length) :
    (B.adjacentSwapLeviEquiv j h R m).val i =
      (B.adjacentSwapRefinement j h i).leviEmbedding R
        (nestedLeviEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R m i) := rfl

/-- Reading an inner matrix entry recovers the corresponding original block entry. -/
@[simp] theorem adjacentSwapLeviEquiv_entry (m : (B.permute (B.adjacentSwap j h)).Levi R)
    (i : Fin (B.adjacentMerge j h).length) (k : Fin (B.adjacentSwapRefinement j h i).length)
    (x y : Fin ((B.adjacentSwapRefinement j h i).size k)) :
    ((refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)).symm
      (B.adjacentSwapLeviEquiv j h R m)) i k x y =
        m (B.adjacentSwapBlockEquiv j h ⟨i, k⟩)
          (Fin.cast (B.adjacentSwapBlock_size j h ⟨i, k⟩) x)
          (Fin.cast (B.adjacentSwapBlock_size j h ⟨i, k⟩) y) := by
  change ((refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)).symm
    (refinedLeviEquiv R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
      (nestedLeviEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R m))) i k x y = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The two descriptions give the same actual ambient matrix. -/
theorem adjacentSwapLeviEmbedding (m : (B.permute (B.adjacentSwap j h)).Levi R) :
    (B.adjacentMerge j h).leviEmbedding R (B.adjacentSwapLeviEquiv j h R m).val =
      (B.permute (B.adjacentSwap j h)).leviEmbedding R m :=
  leviEmbedding_leviRefinementEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R (B.adjacentSwap_index j h) m

/-- The inner and outer triangularity conditions recover the actual standard parabolic. -/
theorem adjacentSwapComposedParabolic_eq :
    Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h) = (B.permute (B.adjacentSwap j h)).parabolic R :=
  composedParabolic_eq_of_coordinates (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R (B.adjacentSwap_index j h)

/-- The parabolic identification retains the underlying ambient matrix. -/
def adjacentSwapParabolicEquiv :
    (B.permute (B.adjacentSwap j h)).parabolic R ≃* Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h) :=
  parabolicRefinementEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R (B.adjacentSwap_index j h)

@[simp] theorem adjacentSwapParabolicEquiv_val (g : (B.permute (B.adjacentSwap j h)).parabolic R) :
    (B.adjacentSwapParabolicEquiv j h R g).val = g.val := rfl

/-- Composed diagonal projection agrees with the original diagonal projection. -/
theorem adjacentSwapComposedLeviProjection (g : (B.permute (B.adjacentSwap j h)).parabolic R) :
    Parabolic.composedLeviProjection R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
      (B.adjacentSwapParabolicEquiv j h R g) =
        B.adjacentSwapLeviEquiv j h R ((B.permute (B.adjacentSwap j h)).leviProjection R g) :=
  composedLeviProjection_parabolicRefinementEquiv (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R (B.adjacentSwap_index j h) g

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The adjacent Levi identification is continuous in both directions. -/
def adjacentSwapLeviEquivContinuous :
    (B.permute (B.adjacentSwap j h)).Levi R ≃ₜ* refinedLevi R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h) :=
  leviRefinementEquivContinuous (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R

@[simp] theorem adjacentSwapLeviEquivContinuous_toMulEquiv :
    (B.adjacentSwapLeviEquivContinuous j h R).toMulEquiv =
      B.adjacentSwapLeviEquiv j h R := rfl

/-- The matrix-preserving parabolic identification is continuous in both directions. -/
def adjacentSwapParabolicEquivContinuous :
    (B.permute (B.adjacentSwap j h)).parabolic R ≃ₜ* Parabolic.composedParabolic R (B.adjacentMerge j h) (B.adjacentSwapRefinement j h) :=
  parabolicRefinementEquivContinuous (B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h) (B.adjacentSwapRefinement j h)
    (B.adjacentSwapBlockEquiv j h) (B.adjacentSwapBlock_size j h) R (B.adjacentSwap_index j h)

@[simp] theorem adjacentSwapParabolicEquivContinuous_toMulEquiv :
    (B.adjacentSwapParabolicEquivContinuous j h R).toMulEquiv =
      B.adjacentSwapParabolicEquiv j h R := rfl

end Topology

end Langlands.GeneralLinear.BlockShape
