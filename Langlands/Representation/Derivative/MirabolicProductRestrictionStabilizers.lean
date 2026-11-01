import Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
import Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits

/-!
# The two orbit stabilizers are the mixed-product inducing subgroups

The stabilizer in `Q = P_((m+1)+(n+1))` of the closed-orbit coset `P` is the
case (II) subgroup `leftSubgroup (m+1) n`, and the stabilizer of the open-orbit
coset `P w⁻¹` is carried by the rank cast onto the case (III) subgroup
`rightSubgroup (n+1) m`. The Levi part of the conjugated element is the
corresponding mixed-product projection.
-/

noncomputable section

namespace Langlands.Derivative.MirabolicProductRestriction

open GeneralLinear GeneralLinear.Mirabolic.MixedProduct

universe u

variable {K : Type u} [Field K] (m n : ℕ)

theorem leftIndex_inl_eq (j : Fin (m + 1)) :
    leftIndex (m + 1) n (Sum.inl j) = Fin.castAdd (n + 1) j :=
  Fin.ext (by simp)

theorem leftIndex_inr_eq (i : Fin (n + 1)) :
    leftIndex (m + 1) n (Sum.inr i) = Fin.natAdd (m + 1) i :=
  Fin.ext (by simp)

/-! ### The closed orbit -/

theorem mem_closedStabilizer_iff (s : mirabolicQ K m n) :
    s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) 1 ↔
      s ∈ leftSubgroup (m + 1) n K := by
  change (MulAut.conj (1 : GeneralLinear ((m + 1) + (n + 1)) K)⁻¹) s.val ∈ parabolicP K m n ↔ _
  rw [inv_one, map_one, MulAut.one_apply, mem_parabolicP_iff, mem_leftSubgroup_iff_entry]
  simp only [leftIndex_inl_eq, leftIndex_inr_eq]

theorem closedStabilizer_levi_zero (s : mirabolicQ K m n)
    (hs : s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) 1) :
    (shape m n).leviProjection K
        (Geometric.stabilizerToInducing (parabolicP K m n) (mirabolicQ K m n) 1 ⟨s, hs⟩)
        (0 : Fin 2) =
      (leftProjection (⟨s, (mem_closedStabilizer_iff m n s).mp hs⟩ :
        leftSubgroup (m + 1) n K)).1 := by
  apply Units.ext
  refine Matrix.ext fun (i : Fin (m + 1)) (j : Fin (m + 1)) => ?_
  change ((MulAut.conj (1 : GeneralLinear ((m + 1) + (n + 1)) K)⁻¹) s.val).val
      ((shape m n).index (0 : Fin 2) i) ((shape m n).index (0 : Fin 2) j) =
    s.val.val (leftIndex (m + 1) n (Sum.inl i)) (leftIndex (m + 1) n (Sum.inl j))
  rw [leftIndex_inl_eq, leftIndex_inl_eq, inv_one, map_one, MulAut.one_apply]
  exact congrArg₂ s.val.val
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) i)
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)

theorem closedStabilizer_levi_one (s : mirabolicQ K m n)
    (hs : s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) 1) :
    (shape m n).leviProjection K
        (Geometric.stabilizerToInducing (parabolicP K m n) (mirabolicQ K m n) 1 ⟨s, hs⟩)
        (1 : Fin 2) =
      (leftProjection (⟨s, (mem_closedStabilizer_iff m n s).mp hs⟩ :
        leftSubgroup (m + 1) n K)).2.val := by
  apply Units.ext
  refine Matrix.ext fun (i : Fin (n + 1)) (j : Fin (n + 1)) => ?_
  change ((MulAut.conj (1 : GeneralLinear ((m + 1) + (n + 1)) K)⁻¹) s.val).val
      ((shape m n).index (1 : Fin 2) i) ((shape m n).index (1 : Fin 2) j) =
    s.val.val (leftIndex (m + 1) n (Sum.inr i)) (leftIndex (m + 1) n (Sum.inr j))
  rw [leftIndex_inr_eq, leftIndex_inr_eq, inv_one, map_one, MulAut.one_apply]
  exact congrArg₂ s.val.val
    (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) i)
    (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)

/-! ### The open orbit -/

variable [TopologicalSpace K]

/-- The rank cast `P_((m+1)+n+1) ≅ P_((n+1)+m+1)` used for the open orbit. -/
abbrev openCast : mirabolic ((m + 1) + n) K ≃ₜ* mirabolic ((n + 1) + m) K :=
  mirabolicCast (show (n + 1) + m = (m + 1) + n by omega).symm

theorem openCast_apply (s : mirabolic ((m + 1) + n) K) (i j : Fin ((n + 1) + m + 1)) :
    (openCast (K := K) m n s).val.val i j =
      s.val.val (finCongr (by omega) i) (finCongr (by omega) j) :=
  mirabolicCast_apply _ s i j

theorem mem_openStabilizer_iff (s : mirabolicQ K m n) :
    s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) (openRep K m n) ↔
      openCast (K := K) m n s ∈ rightSubgroup (n + 1) m K := by
  change (MulAut.conj (openRep K m n)⁻¹) s.val ∈ parabolicP K m n ↔ _
  rw [MulAut.conj_apply, inv_inv, mem_parabolicP_iff, mem_rightSubgroup_iff_entry]
  simp only [openRep_conj_apply, openIndex_castAdd, openIndex_natAdd, openCast_apply]

theorem openStabilizer_levi_zero (s : mirabolicQ K m n)
    (hs : s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) (openRep K m n)) :
    (shape m n).leviProjection K
        (Geometric.stabilizerToInducing (parabolicP K m n) (mirabolicQ K m n) (openRep K m n)
          ⟨s, hs⟩) (0 : Fin 2) =
      (rightProjection (⟨openCast (K := K) m n s, (mem_openStabilizer_iff m n s).mp hs⟩ :
        rightSubgroup (n + 1) m K)).1.val := by
  apply Units.ext
  refine Matrix.ext fun (i : Fin (m + 1)) (j : Fin (m + 1)) => ?_
  change ((MulAut.conj (openRep K m n)⁻¹) s.val).val
      ((shape m n).index (0 : Fin 2) i) ((shape m n).index (0 : Fin 2) j) =
    (openCast (K := K) m n s).val.val (rightIndex (n + 1) m (Sum.inl i))
      (rightIndex (n + 1) m (Sum.inl j))
  rw [openCast_apply, MulAut.conj_apply, inv_inv]
  refine (congrArg₂ (((openRep K m n)⁻¹ * s.val * openRep K m n).val)
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) i)
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)).trans ?_
  rw [openRep_conj_apply, openIndex_castAdd, openIndex_castAdd]

theorem openStabilizer_levi_one (s : mirabolicQ K m n)
    (hs : s ∈ Geometric.orbitStabilizer (parabolicP K m n) (mirabolicQ K m n) (openRep K m n)) :
    (shape m n).leviProjection K
        (Geometric.stabilizerToInducing (parabolicP K m n) (mirabolicQ K m n) (openRep K m n)
          ⟨s, hs⟩) (1 : Fin 2) =
      (rightProjection (⟨openCast (K := K) m n s, (mem_openStabilizer_iff m n s).mp hs⟩ :
        rightSubgroup (n + 1) m K)).2 := by
  apply Units.ext
  refine Matrix.ext fun (i : Fin (n + 1)) (j : Fin (n + 1)) => ?_
  change ((MulAut.conj (openRep K m n)⁻¹) s.val).val
      ((shape m n).index (1 : Fin 2) i) ((shape m n).index (1 : Fin 2) j) =
    (openCast (K := K) m n s).val.val (rightIndex (n + 1) m (Sum.inr i))
      (rightIndex (n + 1) m (Sum.inr j))
  rw [openCast_apply, MulAut.conj_apply, inv_inv]
  refine (congrArg₂ (((openRep K m n)⁻¹ * s.val * openRep K m n).val)
    (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) i)
    (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)).trans ?_
  rw [openRep_conj_apply, openIndex_natAdd, openIndex_natAdd]

end Langlands.Derivative.MirabolicProductRestriction
