import Langlands.Group.GL.Transvection
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Ring.Commute

namespace Langlands.GeneralLinear.OppositeRootNonsolvable

universe u

variable {K : Type u} [Field K] {n : ℕ}

open scoped commutatorElement

@[simp] theorem transvection_inv (i j : Fin n) (hij : i ≠ j) (c : K) :
    (transvectionUnit i j hij c)⁻¹ = transvectionUnit i j hij (-c) := by
  apply Units.ext
  rfl

theorem transvection_mul (i j : Fin n) (hij : i ≠ j) (a b : K) :
    transvectionUnit i j hij a * transvectionUnit i j hij b =
      transvectionUnit i j hij (a + b) := by
  apply Units.ext
  exact Matrix.transvection_mul_transvection_same i j hij a b

/-- A Weyl element supported on two coordinates, expressed in root elements. -/
def rootWeyl (i j : Fin n) (hij : i ≠ j) (s : K) : Langlands.GeneralLinear n K :=
  transvectionUnit i j hij s * transvectionUnit j i hij.symm (-s⁻¹) *
    transvectionUnit i j hij s

/-- The determinant-one diagonal element, expressed using opposite roots. -/
def rootDiagonal (i j : Fin n) (hij : i ≠ j) (s : K) :
    Langlands.GeneralLinear n K :=
  rootWeyl i j hij s * rootWeyl i j hij (-1)

theorem rootWeyl_val (i j : Fin n) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    (rootWeyl i j hij s).val =
      1 + Matrix.single i i (-1) + Matrix.single j j (-1) +
        Matrix.single i j s + Matrix.single j i (-s⁻¹) := by
  change (Matrix.transvection i j s * Matrix.transvection j i (-s⁻¹)) *
    Matrix.transvection i j s = _
  simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext r t
  by_cases hri : i = r <;> by_cases hrj : j = r <;>
    by_cases hti : i = t <;> by_cases htj : j = t <;>
      simp_all [Matrix.one_apply, eq_comm]

theorem rootDiagonal_val (i j : Fin n) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    (rootDiagonal i j hij s).val =
      Matrix.diagonal (fun r => if r = i then s else if r = j then s⁻¹ else 1) := by
  change (rootWeyl i j hij s).val * (rootWeyl i j hij (-1)).val = _
  rw [rootWeyl_val i j hij s hs, rootWeyl_val i j hij (-1) (neg_ne_zero.mpr one_ne_zero)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  ext r t
  by_cases hri : i = r <;> by_cases hrj : j = r <;>
    by_cases hti : i = t <;> by_cases htj : j = t <;>
      simp_all [Matrix.one_apply, Matrix.diagonal_apply, eq_comm]

theorem rootDiagonal_mul_transvection (i j : Fin n) (hij : i ≠ j)
    (s c : K) (hs : s ≠ 0) :
    rootDiagonal i j hij s * transvectionUnit i j hij c =
      transvectionUnit i j hij (s * s * c) * rootDiagonal i j hij s := by
  apply Units.ext
  change (rootDiagonal i j hij s).val * Matrix.transvection i j c =
    Matrix.transvection i j (s * s * c) * (rootDiagonal i j hij s).val
  rw [rootDiagonal_val i j hij s hs]
  ext r t
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hti : t = i <;> by_cases htj : t = j <;>
      simp_all [Matrix.transvection, Matrix.one_apply, eq_comm]
  field_simp

theorem rootDiagonal_commutator (i j : Fin n) (hij : i ≠ j)
    (s c : K) (hs : s ≠ 0) :
    ⁅rootDiagonal i j hij s, transvectionUnit i j hij c⁆ =
      transvectionUnit i j hij ((s * s - 1) * c) := by
  rw [commutatorElement_def, rootDiagonal_mul_transvection i j hij s c hs]
  simp only [mul_assoc, mul_inv_cancel_left, transvection_inv]
  rw [transvection_mul]
  congr 1
  ring

theorem rootDiagonal_mem (H : Subgroup (Langlands.GeneralLinear n K))
    (i j : Fin n) (hij : i ≠ j)
    (hU : ∀ c : K, transvectionUnit i j hij c ∈ H)
    (hL : ∀ c : K, transvectionUnit j i hij.symm c ∈ H) (s : K) :
    rootDiagonal i j hij s ∈ H := by
  exact H.mul_mem (H.mul_mem (H.mul_mem (hU s) (hL (-s⁻¹))) (hU s))
    (H.mul_mem (H.mul_mem (hU (-1)) (hL (-(-1 : K)⁻¹))) (hU (-1)))

/-- Every root element is a commutator in a group containing both opposite roots. -/
theorem transvection_mem_commutator [Infinite K]
    (H : Subgroup (Langlands.GeneralLinear n K))
    (i j : Fin n) (hij : i ≠ j)
    (hU : ∀ c : K, transvectionUnit i j hij c ∈ H)
    (hL : ∀ c : K, transvectionUnit j i hij.symm c ∈ H) (c : K) :
    transvectionUnit i j hij c ∈ ⁅H, H⁆ := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  have hss : s * s - 1 ≠ 0 := by
    intro h
    rcases mul_self_eq_one_iff.mp (sub_eq_zero.mp h) with h | h
    · exact hs.2.1 h
    · exact hs.2.2 h
  have hm := Subgroup.commutator_mem_commutator (rootDiagonal_mem H i j hij hU hL s)
    (hU (c / (s * s - 1)))
  rw [rootDiagonal_commutator i j hij s _ hs.1] at hm
  have hc : (s * s - 1) * (c / (s * s - 1)) = c := mul_div_cancel₀ c hss
  rwa [hc] at hm

/-- Opposite root groups over an infinite field obstruct abstract solvability. -/
theorem not_isSolvable [Infinite K]
    (H : Subgroup (Langlands.GeneralLinear n K))
    (i j : Fin n) (hij : i ≠ j)
    (hU : ∀ c : K, transvectionUnit i j hij c ∈ H)
    (hL : ∀ c : K, transvectionUnit j i hij.symm c ∈ H) :
    ¬ Group.IsSolvable H := by
  have hpersist : ∀ m : ℕ,
      (∀ c : K, transvectionUnit i j hij c ∈ (derivedSeries H m).map H.subtype) ∧
      (∀ c : K, transvectionUnit j i hij.symm c ∈ (derivedSeries H m).map H.subtype) := by
    intro m
    induction m with
    | zero => simpa only [derivedSeries_zero, Subgroup.map_top, H.range_subtype] using
        And.intro hU hL
    | succ m ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator]
      exact ⟨transvection_mem_commutator _ i j hij ih.1 ih.2,
        transvection_mem_commutator _ j i hij.symm ih.2 ih.1⟩
  let x : H := ⟨transvectionUnit i j hij 1, hU 1⟩
  apply not_isSolvable_of_mem_derivedSeries (g := x)
  · intro hx
    have he := congrArg (fun y : H => y.val.val i j) hx
    simp [x, transvectionUnit, Matrix.transvection, hij] at he
  · intro m
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp ((hpersist m).1 1)

end Langlands.GeneralLinear.OppositeRootNonsolvable
