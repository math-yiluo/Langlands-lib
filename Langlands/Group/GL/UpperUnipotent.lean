import Langlands.Group.GL.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# The full upper unipotent matrix group
-/

namespace Langlands.GeneralLinear

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem upperTriangular_mul_diag {A C : Matrix (Fin n) (Fin n) R}
    (hA : A.IsUpperTriangular) (hC : C.IsUpperTriangular) (i : Fin n) :
    (A * C) i i = A i i * C i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hC hij, mul_zero]

/-- Actual upper triangular invertible matrices with all diagonal entries one. -/
def upperUnipotent (n : ℕ) (R : Type u) [CommRing R] :
    Subgroup (Langlands.GeneralLinear n R) where
  carrier := {g | g.val.IsUpperTriangular ∧ ∀ i, g i i = 1}
  one_mem' := ⟨Matrix.blockTriangular_one, by intro i; simp⟩
  mul_mem' := by
    intro g h hg hh
    refine ⟨hg.1.mul hh.1, fun i => ?_⟩
    change (g.val * h.val) i i = 1
    rw [upperTriangular_mul_diag hg.1 hh.1, hg.2 i, hh.2 i, one_mul]
  inv_mem' := by
    intro g hg
    let := g.invertible
    have hi : (g⁻¹).val.IsUpperTriangular := by
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using
        Matrix.blockTriangular_inv_of_blockTriangular hg.1
    refine ⟨hi, fun i => ?_⟩
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i i) g.mul_inv
    rw [upperTriangular_mul_diag hg.1 hi, hg.2 i, one_mul] at h
    simpa using h

namespace UpperUnipotent

/-- Strictly lower entries vanish. -/
theorem entry_eq_zero (g : upperUnipotent n R) {i j : Fin n} (h : j < i) :
    g.val i j = 0 :=
  g.property.1 h

/-- Every diagonal entry is one. -/
@[simp] theorem entry_diag (g : upperUnipotent n R) (i : Fin n) :
    g.val i i = 1 :=
  g.property.2 i

/-- Adjacent upper entries add under multiplication of unipotent matrices. -/
theorem mul_adjacent_entry (g h : upperUnipotent (n + 1) R) (i : Fin n) :
    (g * h).val i.castSucc i.succ =
      g.val i.castSucc i.succ + h.val i.castSucc i.succ := by
  change (g.val.val * h.val.val) i.castSucc i.succ = _
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_add_of_mem i.castSucc i.succ
    (Finset.mem_univ _) (Finset.mem_univ _) (by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega)]
  · rw [entry_diag, entry_diag, one_mul, mul_one, add_comm]
  · rintro j _ ⟨hji, hjs⟩
    by_cases hj : j < i.castSucc
    · rw [entry_eq_zero g hj, zero_mul]
    · have hij : i.succ < j := by
        have hne₁ : j.val ≠ i.val := by
          intro h
          exact hji (Fin.ext h)
        have hne₂ : j.val ≠ i.val + 1 := by
          intro h
          exact hjs (Fin.ext h)
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at *
        omega
      rw [entry_eq_zero h hij, mul_zero]

/-- A single first-superdiagonal coordinate as a homomorphism to the additive ring. -/
def adjacentEntry (i : Fin n) :
    upperUnipotent (n + 1) R →* Multiplicative R where
  toFun g := Multiplicative.ofAdd (g.val i.castSucc i.succ)
  map_one' := by
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ = 0
    simp [ne_of_lt i.castSucc_lt_succ]
  map_mul' g h := mul_adjacent_entry g h i

/-- The sum of adjacent upper entries, ready for composition with an additive character. -/
def superdiagonalSum : upperUnipotent (n + 1) R →* Multiplicative R where
  toFun g := Multiplicative.ofAdd (∑ i : Fin n, g.val i.castSucc i.succ)
  map_one' := by
    change (∑ i : Fin n,
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ) = 0
    apply Finset.sum_eq_zero
    intro i _
    simp [ne_of_lt i.castSucc_lt_succ]
  map_mul' g h := by
    change (∑ i : Fin n, (g * h).val i.castSucc i.succ) =
      (∑ i : Fin n, g.val i.castSucc i.succ) + (∑ i : Fin n, h.val i.castSucc i.succ)
    simp only [mul_adjacent_entry, Finset.sum_add_distrib]

/-- Inverting a unipotent matrix negates every adjacent upper entry. -/
@[simp] theorem inv_adjacent_entry (g : upperUnipotent (n + 1) R) (i : Fin n) :
    (g⁻¹).val i.castSucc i.succ = -g.val i.castSucc i.succ :=
  (adjacentEntry i).map_inv g

section Topology

variable [TopologicalSpace R]

/-- Every matrix entry on the unipotent group is continuous. -/
def entry (i j : Fin n) : C(upperUnipotent n R, R) where
  toFun g := g.val i j
  continuous_toFun := (GeneralLinear.entry i j).continuous.comp continuous_subtype_val

/-- Continuity of each adjacent entry needs only the coefficient topology. -/
def adjacentEntryContinuous (i : Fin n) :
    ContinuousMonoidHom (upperUnipotent (n + 1) R) (Multiplicative R) where
  toMonoidHom := adjacentEntry i
  continuous_toFun :=
    continuous_ofAdd.comp (entry (R := R) i.castSucc i.succ).continuous

variable [IsTopologicalRing R]

/-- The first-superdiagonal sum is a continuous homomorphism. -/
def superdiagonalSumContinuous :
    ContinuousMonoidHom (upperUnipotent (n + 1) R) (Multiplicative R) where
  toMonoidHom := superdiagonalSum
  continuous_toFun := continuous_ofAdd.comp
    (continuous_finsetSum Finset.univ fun i _ =>
      (entry (R := R) (i : Fin n).castSucc i.succ).continuous)

variable [T2Space R]

omit [IsTopologicalRing R] in
/-- The full upper unipotent group is closed in the actual general linear group. -/
theorem isClosed : IsClosed (upperUnipotent n R : Set (Langlands.GeneralLinear n R)) := by
  change IsClosed {g : Langlands.GeneralLinear n R |
    g.val.IsUpperTriangular ∧ ∀ i, g i i = 1}
  apply IsClosed.inter
  · exact isClosed_setOfPred_blockTriangular.preimage
      (show Continuous (fun g : Langlands.GeneralLinear n R => g.val)
        from Units.continuous_val)
  · have hi (i : Fin n) : IsClosed {g : Langlands.GeneralLinear n R | g i i = 1} :=
      isClosed_eq (GeneralLinear.entry (R := R) i i).continuous continuous_const
    have he : {g : Langlands.GeneralLinear n R | ∀ i : Fin n, g i i = 1} =
        ⋂ i : Fin n, {g : Langlands.GeneralLinear n R | g i i = 1} :=
      Set.ofPred_forall _
    change IsClosed {g : Langlands.GeneralLinear n R | ∀ i : Fin n, g i i = 1}
    rw [he]
    exact isClosed_iInter hi

omit [IsTopologicalRing R] in
/-- Closedness supplies local compactness from that of the ambient matrix group. -/
theorem locallyCompactSpace [LocallyCompactSpace (Langlands.GeneralLinear n R)] :
    LocallyCompactSpace (upperUnipotent n R) :=
  (isClosed (R := R) (n := n)).locallyCompactSpace

end Topology
end UpperUnipotent
end Langlands.GeneralLinear
