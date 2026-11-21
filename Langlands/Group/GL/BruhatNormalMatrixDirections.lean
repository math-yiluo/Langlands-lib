import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite

/-! # The lower matrix directions transverse to an upper Bruhat cell -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [Field F] {n : ℕ}

/-- A strictly lower entry stays strictly lower under conjugation by
the inverse permutation matrix. These entries give the normal complement. -/
def bruhatNormalEntry (w : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  j < i ∧ w.symm j < w.symm i

/-- Every permutation other than the long Weyl element has a
simple lower root in the normal complement. -/
theorem exists_simple_bruhatNormalEntry {r : ℕ} (w : Equiv.Perm (Fin (r + 1)))
    (hw : w ≠ Fin.revPerm) :
    ∃ i : Fin r, bruhatNormalEntry w i.succ i.castSucc := by
  by_contra! hn
  have hanti : StrictAnti (w.symm : Fin (r + 1) → Fin (r + 1)) := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    have h : ¬ w.symm i.castSucc < w.symm i.succ :=
      fun h => hn i ⟨Fin.castSucc_lt_succ, h⟩
    exact lt_of_le_of_ne (le_of_not_gt h)
      (fun he => (Fin.castSucc_lt_succ (i := i)).ne (w.symm.injective he).symm)
  have hmono : StrictMono (fun i : Fin (r + 1) => (w.symm i).rev) :=
    fun _ _ h => Fin.rev_lt_rev.mpr (hanti h)
  apply hw
  apply Equiv.ext
  intro i
  have h := congrFun hmono.eq_id (w i)
  simpa using h.symm

/-- Conjugating an elementary lower simple matrix by an upper matrix
retains only its original lower entry, up to its diagonal scalar. -/
theorem conjugate_lowerSimple_sub_isUpperTriangular {r : ℕ}
    (b : upperTriangularSubgroup (r + 1) F) (i : Fin r) (z : F) :
    let c := (b⁻¹ : upperTriangularSubgroup (r + 1) F).val.val
    let a := b.val.val
    let y := c i.succ i.succ * z * a i.castSucc i.castSucc
    (c * Matrix.single i.succ i.castSucc z * a -
      Matrix.single i.succ i.castSucc y).IsUpperTriangular := by
  intro c a y j k hkj
  change k < j at hkj
  have hb : a.IsUpperTriangular := b.property
  have hc : c.IsUpperTriangular :=
    (b⁻¹ : upperTriangularSubgroup (r + 1) F).property
  have hentry : (c * Matrix.single i.succ i.castSucc z * a) j k =
      c j i.succ * z * a i.castSucc k := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i.castSucc]
    · rw [Matrix.mul_single_apply_same]
    · intro l _ hl
      rw [Matrix.mul_single_apply_of_ne z i.succ i.castSucc j l hl c, zero_mul]
    · simp
  rw [Matrix.sub_apply, hentry]
  by_cases he : j = i.succ ∧ k = i.castSucc
  · obtain ⟨rfl, rfl⟩ := he
    change y - Matrix.single i.succ i.castSucc y i.succ i.castSucc = 0
    simp
  · have hzero : c j i.succ * z * a i.castSucc k = 0 := by
      by_contra hn
      have hj : j ≤ i.succ := le_of_not_gt fun h => hn (by
        have hzero : c j i.succ = 0 := hc h
        rw [hzero, zero_mul, zero_mul])
      have hk : i.castSucc ≤ k := le_of_not_gt fun h => hn (by
        have hzero : a i.castSucc k = 0 := hb h
        rw [hzero, mul_zero])
      apply he
      have hj' : j.val ≤ i.val + 1 := hj
      have hk' : i.val ≤ k.val := hk
      have hkj' : k.val < j.val := hkj
      exact ⟨Fin.ext (by simpa only [Fin.val_succ] using (show j.val = i.val + 1 by omega)),
        Fin.ext (by simpa only [Fin.val_castSucc] using (show k.val = i.val by omega))⟩
    have hne : ¬ (i.succ = j ∧ i.castSucc = k) :=
      fun h => he ⟨h.1.symm, h.2.symm⟩
    simp [hzero, Matrix.single, hne]

/-- If a matrix is supported on the normal entries, its upper
conjugate cannot vanish on all those entries unless it is zero. -/
theorem eq_zero_of_upperConjugation_normalEntries (w : Equiv.Perm (Fin n))
    (b : upperTriangularSubgroup n F) (X : Matrix (Fin n) (Fin n) F)
    (hX : ∀ i j, ¬ bruhatNormalEntry w i j → X i j = 0)
    (hY : ∀ i j, bruhatNormalEntry w i j →
      ((b⁻¹ : upperTriangularSubgroup n F).val.val * X * b.val.val) i j = 0) :
    X = 0 := by
  classical
  by_contra hne
  let S := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => X p.1 p.2 ≠ 0)
  have hs : S.Nonempty := by
    by_contra hn
    apply hne
    ext i j
    change X i j = 0
    by_contra hij
    exact hn ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun q => q.1.val - q.2.val) hs
  rcases p with ⟨i, j⟩
  have hXij : X i j ≠ 0 := (Finset.mem_filter.mp hp).2
  have hij : bruhatNormalEntry w i j := by
    by_contra hn
    exact hXij (hX i j hn)
  let a := b.val.val
  let c := (b⁻¹ : upperTriangularSubgroup n F).val.val
  have ha : a.IsUpperTriangular := b.property
  have hc : c.IsUpperTriangular := (b⁻¹ : upperTriangularSubgroup n F).property
  have hkill (k l : Fin n) (hkl : k ≠ i ∨ l ≠ j) : c i k * X k l * a l j = 0 := by
    by_contra hn
    have hik : i ≤ k := le_of_not_gt fun h => hn (by rw [hc h, zero_mul, zero_mul])
    have hlj : l ≤ j := le_of_not_gt fun h => hn (by rw [ha h, mul_zero])
    have hXkl : X k l ≠ 0 := fun h => hn (by rw [h, mul_zero, zero_mul])
    have hh : k.val - l.val ≤ i.val - j.val :=
      hmax (k, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hXkl⟩)
    have hi' : i.val ≤ k.val := hik
    have hj' : l.val ≤ j.val := hlj
    have hij' : j.val < i.val := hij.1
    have hk : k = i := Fin.ext (by omega)
    have hl : l = j := Fin.ext (by omega)
    exact hkl.elim (fun h => h hk) (fun h => h hl)
  have he : (c * X * a) i j = c i i * X i j * a j j := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · exact fun k _ hk => hkill k j (Or.inl hk)
      · simp
    · intro l _ hl
      exact Finset.sum_eq_zero fun k _ => hkill k l (Or.inr hl)
    · simp
  have hci : c i i ≠ 0 :=
    UpperBruhatCoordinates.diag_ne_zero_of_upper _ hc i
  have haj : a j j ≠ 0 :=
    UpperBruhatCoordinates.diag_ne_zero_of_upper _ ha j
  exact (mul_ne_zero (mul_ne_zero hci hXij) haj) (he.symm.trans (hY i j hij))

end Langlands.GeneralLinear
