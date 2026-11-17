import Langlands.Group.GL.LowerBlockLocalizationCoordinates

/-! # Trailing minors in rectangular Iwasawa coordinates -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

variable {R : Type u} [CommRing R] {a d : ℕ}

/-- Columns of the trailing principal minor, with one column replaced by a
leading column. -/
def coordinateMinorColumns (a d : ℕ) (i : Fin d) (j : Fin a) :
    Fin d → Fin (a + d) :=
  Function.update (Fin.natAdd a) i (j.castAdd d)

/-- An upper triangular left factor acts on its trailing rows through its
trailing square block. -/
theorem trailing_submatrix_mul
    (A B : Matrix (Fin (a + d)) (Fin (a + d)) R)
    (hA : A.IsUpperTriangular) (c : Fin d → Fin (a + d)) :
    (A * B).submatrix (Fin.natAdd a) c =
      A.submatrix (Fin.natAdd a) (Fin.natAdd a) *
        B.submatrix (Fin.natAdd a) c := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_add]
  have hz : ∑ k : Fin a, A (i.natAdd a) (k.castAdd d) * B (k.castAdd d) (c j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : (k.castAdd d : Fin (a + d)) < i.natAdd a := by
      change k.val < a + i.val
      omega
    have hAk : A (i.natAdd a) (k.castAdd d) = 0 :=
      hA (i := i.natAdd a) (j := k.castAdd d) hk
    rw [hAk, zero_mul]
  rw [hz, zero_add]

/-- Every trailing minor acquires the product of the corresponding diagonal
entries under upper triangular left multiplication. -/
theorem det_trailing_submatrix_mul
    (A B : Matrix (Fin (a + d)) (Fin (a + d)) R)
    (hA : A.IsUpperTriangular) (c : Fin d → Fin (a + d)) :
    ((A * B).submatrix (Fin.natAdd a) c).det =
      (∏ i : Fin d, A (i.natAdd a) (i.natAdd a)) *
        (B.submatrix (Fin.natAdd a) c).det := by
  rw [trailing_submatrix_mul A B hA c, Matrix.det_mul]
  congr 1
  apply Matrix.det_of_isUpperTriangular
  intro i j hij
  exact hA (by simpa using hij)

/-- A rectangular coordinate is the minor obtained by replacing one trailing
identity column by a column from the leading block. -/
theorem lowerBlockPair_coordinate_minor
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R)
    (i : Fin d) (j : Fin a) :
    ((lowerBlockPair g x 1).val.submatrix (Fin.natAdd a)
      (coordinateMinorColumns a d i j)).det = x i j := by
  classical
  unfold coordinateMinorColumns
  have hm : (lowerBlockPair g x 1).val.submatrix (Fin.natAdd a)
        (Function.update (Fin.natAdd a) i (j.castAdd d)) =
      (1 : Matrix (Fin d) (Fin d) R).updateCol i (fun q => x q j) := by
    ext q s
    by_cases hs : s = i
    · subst s
      simp
    · simp [hs]
  rw [hm]
  simpa [Matrix.one_apply] using
    Matrix.det_updateCol_sum (1 : Matrix (Fin d) (Fin d) R) i (fun q => x q j)

/-- The principal trailing minor of the rectangular chart is one. -/
theorem lowerBlockPair_trailing_minor
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R) :
    ((lowerBlockPair g x 1).val.submatrix (Fin.natAdd a) (Fin.natAdd a)).det = 1 := by
  have hm : (lowerBlockPair g x 1).val.submatrix (Fin.natAdd a) (Fin.natAdd a) =
      (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    simp
  rw [hm, Matrix.det_one]

end Langlands.GeneralLinear.RectangularIwasawa
