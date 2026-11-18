import Langlands.GroupScheme.OddOrthogonalMatrix.Form
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Polynomial unipotent families for the odd split quadratic form -/

noncomputable section

open scoped Matrix

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]
  {R : Type*} [CommRing R]

/-- The ordinary split odd quadratic polynomial over any coefficient ring. -/
def value (x : Index l → R) : R :=
  x (Sum.inl ()) * x (Sum.inl ()) +
    ∑ i, x (Sum.inr (Sum.inl i)) * x (Sum.inr (Sum.inr i))

/-- The polynomial matrix for a short-root parameter on either hyperbolic half.
It changes the axis coordinate by `t` times the paired coordinate. -/
def shortMatrix (a : l ⊕ l) (t : R) : Matrix (Index l) (Index l) R :=
  1 + Matrix.single (Sum.inl ()) (Sum.inr a) (-2 * t) +
    Matrix.single (Sum.inr a.swap) (Sum.inl ()) t +
    Matrix.single (Sum.inr a.swap) (Sum.inr a) (-(t * t))

omit [Fintype l] in
@[simp] theorem shortMatrix_zero (a : l ⊕ l) : shortMatrix a (0 : R) = 1 := by
  simp [shortMatrix]

private theorem single_mul_single_eq (i j k m : Index l) (r s : R) :
    Matrix.single i j r * Matrix.single k m s =
      if j = k then Matrix.single i m (r * s) else 0 := by
  by_cases h : j = k
  · subst k
    simp
  · simp only [ite_eq_right h]
    exact Matrix.single_mul_single_of_ne r i j k h s

/-- The family is additive in its parameter in every characteristic. -/
theorem shortMatrix_add (a : l ⊕ l) (s t : R) :
    shortMatrix a (s + t) = shortMatrix a s * shortMatrix a t := by
  have ha : a ≠ a.swap := by cases a <;> simp
  simp only [shortMatrix, add_mul, mul_add, one_mul, mul_one, single_mul_single_eq]
  simp only [Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inr.injEq, ha,
    ite_false, ite_true, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> ring

/-- The parameter family consists of invertible matrices. -/
def shortUnits (a : l ⊕ l) : Multiplicative R →* (Matrix (Index l) (Index l) R)ˣ where
  toFun t :=
    { val := shortMatrix a t.toAdd
      inv := shortMatrix a (-t.toAdd)
      val_inv := by rw [← shortMatrix_add, add_neg_cancel, shortMatrix_zero]
      inv_val := by rw [← shortMatrix_add, neg_add_cancel, shortMatrix_zero] }
  map_one' := Units.ext (shortMatrix_zero a)
  map_mul' s t := Units.ext (shortMatrix_add a s.toAdd t.toAdd)

omit [Fintype l] in
/-- The entry mapping the paired coordinate into the axis recovers the parameter. -/
@[simp] theorem shortMatrix_axis_entry (a : l ⊕ l) (t : R) :
    shortMatrix a t (Sum.inr a.swap) (Sum.inl ()) = t := by
  simp [shortMatrix]

/-- The additive parameter is visible in every coefficient ring. -/
theorem shortUnits_injective (a : l ⊕ l) : Function.Injective (shortUnits (R := R) a) := by
  intro s t h
  have h' := congrArg (fun g : (Matrix (Index l) (Index l) R)ˣ =>
    (g : Matrix (Index l) (Index l) R) (Sum.inr a.swap) (Sum.inl ())) h
  change shortMatrix a s.toAdd (Sum.inr a.swap) (Sum.inl ()) =
    shortMatrix a t.toAdd (Sum.inr a.swap) (Sum.inl ()) at h'
  simpa using h'

/-- The short matrix factors into three elementary transvections. -/
theorem shortMatrix_factor (a : l ⊕ l) (t : R) :
    shortMatrix a t =
      Matrix.transvection (Sum.inr a.swap) (Sum.inl ()) t *
        Matrix.transvection (Sum.inl ()) (Sum.inr a) (-2 * t) *
        Matrix.transvection (Sum.inr a.swap) (Sum.inr a) (t * t) := by
  have ha : a ≠ a.swap := by cases a <;> simp
  simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, single_mul_single_eq]
  simp only [Sum.inl_ne_inr, Sum.inr.injEq, ha, single_mul_single_eq,
    ite_false, ite_true, add_zero]
  ext i j
  simp only [shortMatrix, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> ring

/-- Every parameter matrix has determinant one over any commutative ring. -/
theorem det_shortMatrix (a : l ⊕ l) (t : R) : (shortMatrix a t).det = 1 := by
  have ha : Sum.inr a.swap ≠ (Sum.inr a : Index l) := by cases a <;> simp
  rw [shortMatrix_factor, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_transvection_of_ne, ha]

/-- The explicit row action of a short matrix. -/
theorem vecMul_shortMatrix (a : l ⊕ l) (t : R) (x : Index l → R) :
    x ᵥ* shortMatrix a t = x + Pi.single (Sum.inr a) (x (Sum.inl ()) * (-2 * t)) +
      Pi.single (Sum.inl ()) (x (Sum.inr a.swap) * t) +
      Pi.single (Sum.inr a) (x (Sum.inr a.swap) * (-(t * t))) := by
  have hs : ∀ (i j : Index l) (r : R),
      x ᵥ* Matrix.single i j r = Pi.single j (x i * r) := by
    intro i j r
    ext k
    simp [Matrix.vecMul, dotProduct, Matrix.single_apply, Pi.single_apply, ite_and, eq_comm]
  simp only [shortMatrix, Matrix.vecMul_add, Matrix.vecMul_one, hs]

/-- The short matrix preserves the full quadratic polynomial over every
commutative coefficient ring, including rings of characteristic two. -/
theorem value_vecMul_shortMatrix (a : l ⊕ l) (t : R) (x : Index l → R) :
    value (x ᵥ* shortMatrix a t) = value x := by
  rw [vecMul_shortMatrix]
  rcases a with a | a <;>
    simp [value, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

omit [Fintype l] in
/-- The parameter matrices commute with every homomorphism of coefficient rings. -/
theorem shortMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (a : l ⊕ l) (t : R) :
    (shortMatrix a t).map f = shortMatrix a (f t) := by
  simp [shortMatrix, Matrix.map_add, Matrix.map_single, _root_.map_ofNat]

end Langlands.GroupScheme.OddOrthogonalMatrix
