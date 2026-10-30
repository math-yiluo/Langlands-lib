import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Classification.MaximalConePolygon

/-! The shared weighted-block to diagonal closed-cone comparison. -/

namespace Langlands.Exponents

open GeneralLinear Geometric MaximalConePolygon
open scoped BigOperators

private theorem block_constant_cone_of_boundaries {n : ℕ} (E : BlockShape n)
    (V : Fin n → ℝ)
    (hconstant : ∀ x y, blockIndex E x = blockIndex E y → V x = V y)
    (htotal : ∑ a, V a = 0)
    (hboundary : ∀ m : ℕ, 0 ≤ pre V (E.startN m)) :
    IsClosedPositiveRootCone V := by
  refine ⟨htotal, ?_⟩
  intro m _hm hmn
  change 0 ≤ pre V m
  let j := blockIndex E ⟨m, hmn⟩
  obtain ⟨hj1, hj2⟩ := E.blockIndex_spec ⟨m, hmn⟩
  refine pre_nonneg_of_antitone V (a := E.startN j)
    (b := E.startN (j.val + 1)) ?_ (hboundary _) (hboundary _) hj1
    (by rw [E.startN_succ]; exact hj2.le)
  intro x y hx hxy hy
  rw [E.startN_succ] at hy
  have hx' : blockIndex E x = j :=
    (E.blockIndex_eq_iff x j).2 ⟨hx, lt_of_le_of_lt (Fin.le_def.mp hxy) hy⟩
  have hy' : blockIndex E y = j :=
    (E.blockIndex_eq_iff y j).2 ⟨le_trans hx (Fin.le_def.mp hxy), hy⟩
  exact (hconstant y x (hy'.trans hx'.symm)).le

private theorem cone_pre_nonneg {n : ℕ} {V : Fin n → ℝ}
    (hV : IsClosedPositiveRootCone V) (m : ℕ) : 0 ≤ pre V m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pre]
  · by_cases hmn : m < n
    · exact hV.2 m hm hmn
    · have hnm : n ≤ m := Nat.le_of_not_gt hmn
      unfold pre
      rw [Finset.filter_true_of_mem (fun a _ => lt_of_lt_of_le a.isLt hnm)]
      exact hV.1.ge

/-- A closed cone of size-weighted block values gives the cone of the repeated diagonal values. -/
theorem diagonal_cone_of_weighted_block_cone {n : ℕ} (E : BlockShape n)
    (f : Fin E.length → ℝ)
    (hf : IsClosedPositiveRootCone (fun i => (E.size i : ℝ) * f i)) :
    IsClosedPositiveRootCone (fun a => f (blockIndex E a)) := by
  classical
  apply block_constant_cone_of_boundaries E
  · intro x y hxy
    rw [hxy]
  · calc
      _ = ∑ k, (E.size k : ℝ) * f k := by
        simpa using E.sum_blockIndex f (fun _ => True)
      _ = 0 := hf.1
  · intro m
    rw [pre_blockIndex_eq E f (E.startN m) (fun k => (k : ℕ) < m)
      (fun a => E.lt_startN_iff a m)]
    exact cone_pre_nonneg hf m

end Langlands.Exponents
