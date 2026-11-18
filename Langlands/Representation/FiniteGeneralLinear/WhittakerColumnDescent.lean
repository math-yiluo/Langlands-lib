import Langlands.Group.GL.MirabolicRadical
import Langlands.Group.GL.RankReindex

/-! Matrix identities for adjoining one column to an upper-unipotent subgroup. -/

noncomputable section

open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
  (radical radicalElement radicalEquiv radicalElement_first radicalElement_last
    radicalElement_bottom levi levi_first levi_last levi_bottom levi_mul_radicalElement)
open scoped BigOperators Matrix

namespace Langlands.FiniteGeneralLinear.WhittakerDescent

variable {k : Type*} [CommRing k] {n : ℕ}

/-- The first `m` columns agree with the identity matrix. -/
def FixesColumns (m : ℕ) (g : GeneralLinear n k) : Prop :=
  ∀ (i j : Fin n), j.val < m → g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j

private theorem mul_entry_fixedColumn (A B : Matrix (Fin n) (Fin n) k) (i j : Fin n)
    (hj : ∀ l, B l j = (1 : Matrix (Fin n) (Fin n) k) l j) :
    (A * B) i j = A i j := by
  simp [Matrix.mul_apply, hj, Matrix.one_apply]

private theorem mul_entry_fixedRow (A B : Matrix (Fin n) (Fin n) k) (i j : Fin n)
    (hi : ∀ l, A i l = (1 : Matrix (Fin n) (Fin n) k) i l) :
    (A * B) i j = B i j := by
  simp [Matrix.mul_apply, hi, Matrix.one_apply]

/-- A change of basis preserving the first `m` coordinate subspace preserves the condition
of fixing it pointwise. -/
theorem FixesColumns.conj {m : ℕ} {u g : GeneralLinear n k} (hu : FixesColumns m u)
    (hg : ∀ (i j : Fin n), m ≤ i.val → j.val < m → g.val i j = 0) :
    FixesColumns m (g⁻¹ * u * g) := by
  intro i j hj
  have he (l : Fin n) : (u.val * g.val) l j = g.val l j := calc
    _ = ((1 : Matrix (Fin n) (Fin n) k) * g.val) l j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val < m
      · rw [hu l t ht]
      · rw [hg t j (Nat.le_of_not_lt ht) hj, mul_zero, mul_zero]
    _ = _ := by rw [one_mul]
  change (((g⁻¹).val * u.val) * g.val) i j = _
  rw [mul_assoc]
  calc
    _ = ((g⁻¹).val * g.val) i j := by simp only [Matrix.mul_apply (M := (g⁻¹).val), he]
    _ = _ := by rw [g.inv_mul]

private theorem rankInclusion_entry {m r : ℕ} (g : GeneralLinear m k) (i j : Fin (m + r)) :
    (rankInclusion r g).val i j =
      if hi : i.val < m then if hj : j.val < m then g.val ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else (1 : Matrix (Fin (m + r)) (Fin (m + r)) k) i j
      else (1 : Matrix (Fin (m + r)) (Fin (m + r)) k) i j := by
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · exact (blockSum_apply_left g 1 _ _).trans (by simp)
  · rename_i i j
    have hne : i.castAdd r ≠ j.natAdd m := by
      intro e
      have := congrArg Fin.val e
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    exact (blockSum_apply_left_right g 1 _ _).trans (by simp [hne])
  · rename_i i j
    have hne : i.natAdd m ≠ j.castAdd r := by
      intro e
      have := congrArg Fin.val e
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    exact (blockSum_apply_right_left g 1 _ _).trans (by simp [hne])
  · exact (blockSum_apply_right g 1 _ _).trans (by simp [Matrix.one_apply])

private def extendRank {m : ℕ} (hm : m ≤ n) : GeneralLinear m k →* GeneralLinear n k :=
  (reindex (finCongr (Nat.add_sub_of_le hm))).toMonoidHom.comp (rankInclusion (n - m))

private theorem extendRank_entry {m : ℕ} (hm : m ≤ n) (g : GeneralLinear m k)
    (i j : Fin n) : (extendRank hm g).val i j =
      if hi : i.val < m then if hj : j.val < m then g.val ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else (1 : Matrix (Fin n) (Fin n) k) i j
      else (1 : Matrix (Fin n) (Fin n) k) i j := by
  change (reindex (finCongr (Nat.add_sub_of_le hm)) (rankInclusion (n - m) g)).val i j = _
  rw [reindex_finCongr_apply, rankInclusion_entry]
  simp [Matrix.one_apply]

private theorem radical_entry {m : ℕ} (x : Fin m → k) (i j : Fin (m + 1)) :
    (radicalElement x).val.val.val i j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j +
      if hi : i.val < m then if j = Fin.last m then x ⟨i.val, hi⟩ else 0 else 0 := by
  induction j using Fin.lastCases with
  | cast j => simp [Matrix.one_apply]
  | last =>
    induction i using Fin.lastCases with
    | cast i => simp
    | last => simp

private def columnGL (p : Fin n) : Multiplicative (Fin p.val → k) →* GeneralLinear n k :=
  (extendRank (Nat.succ_le_of_lt p.isLt)).comp
    ((mirabolic p.val k).subtype.comp ((radical p.val k).subtype.comp
      radicalEquiv.symm.toMonoidHom))

private theorem columnGL_entry (p : Fin n) (x : Fin p.val → k) (i j : Fin n) :
    (columnGL p (Multiplicative.ofAdd x)).val i j =
      (1 : Matrix (Fin n) (Fin n) k) i j +
        if hi : i.val < p.val then if j = p then x ⟨i.val, hi⟩ else 0 else 0 := by
  change (extendRank (Nat.succ_le_of_lt p.isLt) (radicalElement x).val.val).val i j = _
  rw [extendRank_entry]
  split <;> rename_i hi
  · split <;> rename_i hj
    · rw [radical_entry]
      have he : (⟨j.val, hj⟩ : Fin (p.val + 1)) = Fin.last p.val ↔ j = p := by
        simp [Fin.ext_iff]
      simp [Matrix.one_apply, Fin.ext_iff, he]
    · have hjp : j ≠ p := by rintro rfl; exact hj (Nat.lt_succ_self _)
      simp [hjp]
  · have hip : ¬ i.val < p.val := by omega
    simp [hip]

/-- The column subgroup at `p`, with entries above `(p,p)` indexed by `Fin p.val`. -/
def column (p : Fin n) : Multiplicative (Fin p.val → k) →* upperUnipotent n k :=
  (columnGL p).codRestrict _ fun x => by
    change columnGL p (Multiplicative.ofAdd x.toAdd) ∈ upperUnipotent n k
    constructor
    · intro i j hji
      change j < i at hji
      rw [columnGL_entry, Matrix.one_apply, ite_eq_right (ne_of_gt hji), zero_add]
      split <;> rename_i hi
      · have hne : j ≠ p := fun h => (Nat.not_lt_of_le hji.le) (h ▸ hi)
        simp [hne]
      · rfl
    · intro i
      rw [columnGL_entry]
      simp only [Matrix.one_apply, ↓reduceIte]
      split <;> rename_i hi
      · have hne : i ≠ p := fun h => (Nat.lt_irrefl _) (h ▸ hi)
        simp [hne]
      · simp

theorem column_entry (p : Fin n) (x : Fin p.val → k) (i j : Fin n) :
    (column p (Multiplicative.ofAdd x)).val.val i j =
      (1 : Matrix (Fin n) (Fin n) k) i j +
        if hi : i.val < p.val then if j = p then x ⟨i.val, hi⟩ else 0 else 0 :=
  columnGL_entry p x i j

/-- A column multiplier changes only the preceding rows. -/
theorem column_mul_entry (p : Fin n) (x : Fin p.val → k) (u : upperUnipotent n k)
    (i j : Fin n) : ((column p (Multiplicative.ofAdd x)) * u).val.val i j = u.val.val i j +
      if hi : i.val < p.val then x ⟨i.val, hi⟩ * u.val.val p j else 0 := by
  change ((column p (Multiplicative.ofAdd x)).val.val * u.val.val) i j = _
  by_cases hi : i.val < p.val
  · simp [Matrix.mul_apply, column_entry, hi, add_mul, Finset.sum_add_distrib, Matrix.one_apply]
  · rw [dite_eq_right hi, add_zero]
    apply mul_entry_fixedRow
    intro l
    simp [column_entry, hi]

/-- Clearing column `p` factors a matrix fixing the first `p.val` columns. -/
theorem column_factor (p : Fin n) (u : upperUnipotent n k) (hu : FixesColumns p.val u.val) :
    ∃ (x : Fin p.val → k) (u' : upperUnipotent n k),
      FixesColumns (p.val + 1) u'.val ∧
      u' = column p (Multiplicative.ofAdd (-x)) * u ∧
      u = column p (Multiplicative.ofAdd x) * u' := by
  let x (i : Fin p.val) := u.val.val (Fin.castLE (Nat.le_of_lt p.isLt) i) p
  let u' := column p (Multiplicative.ofAdd (-x)) * u
  refine ⟨x, u', ?_, rfl, ?_⟩
  · intro i j hj
    change (column p (Multiplicative.ofAdd (-x)) * u).val.val i j = _
    rw [column_mul_entry]
    by_cases h : j.val < p.val
    · rw [hu i j h, UpperUnipotent.entry_eq_zero u h]
      split <;> simp
    · have hjp : j = p := Fin.ext (by omega)
      subst j
      rw [UpperUnipotent.entry_diag, Matrix.one_apply]
      by_cases hi : i.val < p.val
      · have hne : i ≠ p := fun e => (Nat.lt_irrefl _) (e ▸ hi)
        rw [dite_eq_left hi, ite_eq_right hne, mul_one]
        have hx : x ⟨i.val, hi⟩ = u.val.val i p := rfl
        simp [hx]
      · rw [dite_eq_right hi, add_zero]
        rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with e | hlt
        · have he : i = p := Fin.ext e.symm
          subst i
          simp
        · have he : p < i := hlt
          rw [UpperUnipotent.entry_eq_zero u he, ite_eq_right (ne_of_gt he)]
  · change u = column p (Multiplicative.ofAdd x) * (column p (Multiplicative.ofAdd (-x)) * u)
    rw [← mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel]
    change u = column p 1 * u
    rw [map_one, one_mul]

/-- The upper-unipotent conjugation by a column multiplier preserves the next stage. -/
theorem fixesColumns_column_conj (p : Fin n) {u : upperUnipotent n k}
    (hu : FixesColumns (p.val + 1) u.val) (x : Fin p.val → k) :
    FixesColumns (p.val + 1)
      ((column p (Multiplicative.ofAdd x))⁻¹ * u * column p (Multiplicative.ofAdd x)).val := by
  apply hu.conj
  intro i j hi hj
  have hne : i ≠ j := fun h => (Nat.not_lt_of_le hi) (h ▸ hj)
  rw [column_entry, Matrix.one_apply, ite_eq_right hne]
  simp [show ¬ i.val < p.val by omega]

/-- Extend the rank-`p.val` Levi by the identity on the remaining coordinates. -/
def headLevi (p : Fin n) : GeneralLinear p.val k →* GeneralLinear n k :=
  (extendRank (Nat.succ_le_of_lt p.isLt)).comp ((mirabolic p.val k).subtype.comp levi)

private theorem levi_entry_of_tail {m : ℕ} (g : GeneralLinear m k) (i j : Fin (m + 1))
    (h : m ≤ i.val ∨ m ≤ j.val) :
    (levi g).val.val i j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j := by
  induction i using Fin.lastCases with
  | last => simp [Matrix.one_apply, eq_comm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => exact (h.elim (Nat.not_le_of_lt i.isLt) (Nat.not_le_of_lt j.isLt)).elim

private theorem headLevi_entry_of_tail (p : Fin n) (g : GeneralLinear p.val k) (i j : Fin n)
    (h : p.val ≤ i.val ∨ p.val ≤ j.val) :
    (headLevi p g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  change (extendRank (Nat.succ_le_of_lt p.isLt) (levi g).val).val i j = _
  rw [extendRank_entry]
  split
  · split
    · rw [levi_entry_of_tail _ _ _ h]
      simp [Matrix.one_apply, Fin.ext_iff]
    · rfl
  · rfl

/-- Levi action on column matrices is the usual action on column vectors. -/
theorem headLevi_mul_column (p : Fin n) (g : GeneralLinear p.val k) (x : Fin p.val → k) :
    headLevi p g * (column p (Multiplicative.ofAdd x)).val =
      (column p (Multiplicative.ofAdd (g.val.mulVec x))).val * headLevi p g := by
  let f := extendRank (k := k) (Nat.succ_le_of_lt p.isLt)
  change f (levi g).val * f (radicalElement x).val.val =
    f (radicalElement (g.val.mulVec x)).val.val * f (levi g).val
  have h := congrArg (fun u : mirabolic p.val k => f u.val) (levi_mul_radicalElement g x)
  change f ((levi g).val * (radicalElement x).val.val) =
    f ((radicalElement (g.val.mulVec x)).val.val * (levi g).val) at h
  simpa only [map_mul] using h

private theorem headLevi_conj_entry_of_tail (p : Fin n) (g : GeneralLinear p.val k)
    (u : upperUnipotent n k) (i j : Fin n) (hi : p.val ≤ i.val) (hj : p.val ≤ j.val) :
    ((headLevi p g)⁻¹ * u.val * headLevi p g).val i j = u.val.val i j := by
  change (((headLevi p g)⁻¹).val * u.val.val * (headLevi p g).val) i j = _
  rw [mul_entry_fixedColumn _ _ _ _ (fun l => headLevi_entry_of_tail p g l j (Or.inr hj)),
    mul_entry_fixedRow]
  intro l
  rw [← map_inv]
  exact headLevi_entry_of_tail p g⁻¹ i l (Or.inl hi)

/-- Conjugation by the embedded Levi preserves the next stage and its trailing block. -/
theorem exists_headLevi_conj (p : Fin n) (g : GeneralLinear p.val k) {u : upperUnipotent n k}
    (hu : FixesColumns (p.val + 1) u.val) :
    ∃ u' : upperUnipotent n k, u'.val = (headLevi p g)⁻¹ * u.val * headLevi p g ∧
      FixesColumns (p.val + 1) u'.val ∧
      ∀ i j : Fin n, p.val ≤ i.val → p.val ≤ j.val → u'.val.val i j = u.val.val i j := by
  let U := (headLevi p g)⁻¹ * u.val * headLevi p g
  have hfixed : FixesColumns (p.val + 1) U := hu.conj fun i j hi hj => by
    have hne : i ≠ j := fun h => (Nat.not_lt_of_le hi) (h ▸ hj)
    rw [headLevi_entry_of_tail p g i j (Or.inl (by omega)), Matrix.one_apply, ite_eq_right hne]
  have htail := headLevi_conj_entry_of_tail p g u
  have hU : U ∈ upperUnipotent n k := by
    constructor
    · intro i j hij
      change j < i at hij
      have hij' : j.val < i.val := hij
      change U.val i j = 0
      by_cases hj : j.val < p.val + 1
      · rw [hfixed i j hj, Matrix.one_apply, ite_eq_right (ne_of_gt hij)]
      · exact (htail i j (by omega) (by omega)).trans
          (UpperUnipotent.entry_eq_zero u hij)
    · intro i
      by_cases hi : i.val < p.val + 1
      · simp [hfixed i i hi]
      · rw [htail i i (by omega) (by omega), UpperUnipotent.entry_diag]
  exact ⟨⟨U, hU⟩, rfl, hfixed, htail⟩

end Langlands.FiniteGeneralLinear.WhittakerDescent
