import Langlands.Group.GL.UpperBruhatProof
import Langlands.Group.GL.Transvection
import Langlands.Group.GL.OppositeRootNonsolvable
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Solvable

namespace Langlands.GeneralLinear.UpperTriangularMaximalSolvable

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem transvection_mem_upper {i j : Fin n} (hij : i < j) (c : K) :
    transvectionUnit i j hij.ne c ∈ upperTriangularSubgroup n K := by
  intro r s hsr
  have hsingle : ¬ (i = r ∧ j = s) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_gt hij) hsr
  have hrs : r ≠ s := ne_of_gt hsr
  simp [transvectionUnit, Matrix.transvection,
    hrs, hsingle]

theorem permutation_conjugate_transvection (w : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i ≠ j) (c : K) :
    permutation n K w * transvectionUnit i j hij c * (permutation n K w)⁻¹ =
      transvectionUnit (w i) (w j) (w.injective.ne hij) c := by
  apply Units.ext
  ext r s
  rw [permutation_conjugate_entry]
  simp [transvectionUnit, Matrix.transvection, Matrix.one_apply,
    Matrix.single_apply, Equiv.eq_symm_apply]

/-- A nonidentity finite permutation has an inversion. -/
theorem exists_inversion (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ i j, i < j ∧ w j < w i := by
  by_contra! h
  apply hw
  apply (w.monotone_iff).mp
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact h i j hij

/-- A subgroup properly containing the upper triangular matrices contains an
entire lower root group. -/
theorem exists_lower_transvections (H : Subgroup (Langlands.GeneralLinear n K))
    (hBH : upperTriangularSubgroup n K ≤ H)
    (hHB : ¬ H ≤ upperTriangularSubgroup n K) :
    ∃ (i j : Fin n) (hji : j < i),
      ∀ c : K, transvectionUnit i j (ne_of_gt hji) c ∈ H := by
  obtain ⟨g, hgH, hgB⟩ := SetLike.not_le_iff_exists.mp hHB
  obtain ⟨a, b, w, ha, hb, hfactor⟩ := fieldUpperBruhatFactorizationTheorem K n g
  have hp : permutation n K w ∈ H := by
    have hm := H.mul_mem (H.mul_mem (H.inv_mem (hBH ha)) hgH)
      (H.inv_mem (hBH hb))
    simpa [hfactor, mul_assoc] using hm
  have hw : w ≠ 1 := by
    intro hw
    apply hgB
    rw [hfactor, hw, map_one, mul_one]
    exact mul_mem ha hb
  obtain ⟨i, j, hij, hwji⟩ := exists_inversion w hw
  refine ⟨w i, w j, hwji, ?_⟩
  intro c
  have hm := H.mul_mem (H.mul_mem hp (hBH (transvection_mem_upper hij c)))
    (H.inv_mem hp)
  simpa only [permutation_conjugate_transvection] using hm

/-- Over an infinite field, every proper overgroup of the upper triangular
subgroup is nonsolvable. -/
theorem not_isSolvable_of_not_le [Infinite K]
    (H : Subgroup (Langlands.GeneralLinear n K))
    (hBH : upperTriangularSubgroup n K ≤ H)
    (hHB : ¬ H ≤ upperTriangularSubgroup n K) : ¬ Group.IsSolvable H := by
  obtain ⟨i, j, hji, hL⟩ := exists_lower_transvections H hBH hHB
  exact OppositeRootNonsolvable.not_isSolvable H i j (ne_of_gt hji) hL
    (fun c => hBH (transvection_mem_upper hji c))

/-- The upper triangular group is maximal among abstract solvable subgroups. -/
theorem eq_upper_of_isSolvable [Infinite K]
    (H : Subgroup (Langlands.GeneralLinear n K))
    (hBH : upperTriangularSubgroup n K ≤ H) (hsolv : Group.IsSolvable H) :
    H = upperTriangularSubgroup n K := by
  apply le_antisymm _ hBH
  by_contra hHB
  exact not_isSolvable_of_not_le H hBH hHB hsolv

end Langlands.GeneralLinear.UpperTriangularMaximalSolvable
