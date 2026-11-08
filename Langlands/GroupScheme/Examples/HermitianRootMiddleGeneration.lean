import Langlands.GroupScheme.Examples.HermitianRootReflectionAction

/-! # Elementary lifts of all anisotropic Hermitian middle isometries -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι] [DecidableEq ι] {c : RingInvolution L}
  {H : DiagonalForm c ι}

/-- Preservation of all pairings of the standard middle columns. -/
def PreservesMiddle (H : DiagonalForm c ι) (T : Matrix ι ι L) : Prop :=
  ∀ i j, H.pairing (fun k => T k i) (fun k => T k j) =
    if i = j then H.weight i else 0

omit [Fintype ι] in
@[simp] theorem leviMatrix_one :
    leviMatrix (c := c) (1 : L) (1 : Matrix ι ι L) = 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [leviMatrix, Matrix.fromBlocks, Matrix.one_apply]

omit [DecidableEq ι] in
theorem leviMatrix_mul (a b : L) (S T : Matrix ι ι L) :
    leviMatrix (c := c) a S * leviMatrix (c := c) b T =
      leviMatrix (c := c) (a * b) (S * T) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [leviMatrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, map_mul, mul_comm]

theorem preservesMiddle_of_levi {a : L} {T : Matrix ι ι L}
    (hT : PreservesForm H (leviMatrix (c := c) a T)) :
    PreservesMiddle H T := by
  intro i j
  have h := preservesForm_entry hT (middleIndex j) (middleIndex i)
  have he : -(H.pairing (fun k => T k i) (fun k => T k j)) =
      -(if i = j then H.weight i else 0) := by
    by_cases hij : i = j
    · subst j
      simpa [leviMatrix, middleIndex, gram, Matrix.fromBlocks,
        Matrix.diagonal_apply, DiagonalForm.pairing,
        mul_comm, mul_left_comm, mul_assoc] using h
    · simpa [leviMatrix, middleIndex, gram, Matrix.fromBlocks,
        Matrix.diagonal_apply, DiagonalForm.pairing, hij, Ne.symm hij,
        mul_comm, mul_left_comm, mul_assoc] using h
  exact neg_injective he

theorem preservesMiddle_of_elementary_levi
    {g : Matrix.GeneralLinearGroup (Index ι) L} (hg : g ∈ elementarySubgroup H)
    {a : L} {T : Matrix ι ι L}
    (hval : (g : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a T) :
    PreservesMiddle H T := by
  have hform : PreservesForm H (g : Matrix (Index ι) (Index ι) L) :=
    (elementarySubgroup_le_specialUnitarySubgroup H hg).1
  rw [hval] at hform
  exact preservesMiddle_of_levi hform

/-- Every middle isometry has an actual elementary lift with some nonzero
hyperbolic coefficient. -/
theorem exists_elementary_levi_middle (hH : H.IsAnisotropic)
    (s : L) (hs : s + c.bar s = 0) (hsne : s ≠ 0)
    (T : Matrix ι ι L) (hT : PreservesMiddle H T) :
    ∃ g ∈ elementarySubgroup H, ∃ a : L, a ≠ 0 ∧
      (g : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a T := by
  have aux (J : Finset ι) :
      ∃ g ∈ elementarySubgroup H, ∃ (a : L) (U : Matrix ι ι L),
        a ≠ 0 ∧ (g : Matrix (Index ι) (Index ι) L) = leviMatrix (c := c) a U ∧
          ∀ j ∈ J, (fun i => U i j) = fun i => T i j := by
    induction J using Finset.induction_on with
    | empty =>
      refine ⟨1, (elementarySubgroup H).one_mem, 1, 1, one_ne_zero, ?_, ?_⟩
      · exact leviMatrix_one.symm
      · simp
    | @insert j J hj ih =>
      obtain ⟨g, hg, a, U, ha, hval, hfix⟩ := ih
      have hU := preservesMiddle_of_elementary_levi hg hval
      let w : ι → L := fun i => U i j
      let v : ι → L := fun i => T i j
      have hnorm : H.pairing w w = H.pairing v v := by
        exact (hU j j).trans (hT j j).symm
      obtain ⟨r, hr, b, R, hb, hrval, hmatch, hrfix⟩ :=
        exists_elementary_levi_between hH s hs hsne w v hnorm
      refine ⟨r * g, (elementarySubgroup H).mul_mem hr hg,
        b * a, R * U, mul_ne_zero hb ha, ?_, ?_⟩
      · change (r : Matrix (Index ι) (Index ι) L) *
          (g : Matrix (Index ι) (Index ι) L) = _
        rw [hrval, hval, leviMatrix_mul]
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hmatch
        · have hperp : H.pairing (fun i => U i k) (w - v) = 0 := by
            rw [DiagonalForm.pairing_sub_right]
            change H.pairing (fun i => U i k) (fun i => U i j) -
              H.pairing (fun i => U i k) (fun i => T i j) = 0
            rw [hU k j, hfix k hk, hT k j, sub_self]
          exact (hrfix (fun i => U i k) hperp).trans (hfix k hk)
  obtain ⟨g, hg, a, U, ha, hval, hfix⟩ := aux Finset.univ
  have hUT : U = T := by
    ext i j
    exact congrFun (hfix j (Finset.mem_univ j)) i
  exact ⟨g, hg, a, ha, hUT ▸ hval⟩

end Langlands.GroupScheme.HermitianRoot
