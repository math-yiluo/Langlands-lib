import Langlands.GroupScheme.OddOrthogonalMatrix.Roots

/-! # The matrix centralizer of the odd diagonal and short families -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

/-- A matrix commuting with the standard torus over all coefficient algebras is diagonal. -/
theorem matrix_eq_diagonal_of_commutes_torus (A : Matrix (Index l) (Index l) K)
    (hA : ∀ (R : Type u) [CommRing R] [Algebra K R] (τ : ULift.{u} l → Rˣ),
      A.map (algebraMap K R) * Matrix.diagonal (fun i => (torusWeights τ i : R)) =
        Matrix.diagonal (fun i => (torusWeights τ i : R)) * A.map (algebraMap K R)) :
    A = Matrix.diagonal (fun i => A i i) := by
  have hoff (x y : Index l) (hxy : x ≠ y) : A x y = 0 := by
    by_contra hne
    apply hxy
    apply weightCoord_injective
    funext c
    have he := congrFun (congrFun (hA K[T;T⁻¹]
      (Pi.mulSingle ⟨c⟩ (Gm.relativeCoordUnit K))) x) y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at he
    rw [torusWeights_mulSingle, torusWeights_mulSingle,
      Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val,
      ← LaurentPolynomial.C_eq_algebraMap] at he
    exact GeneralLinear.exponent_eq_of_C_mul_T hne he
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij, hoff i j hij]

/-- Adding the short parameter-one families forces every diagonal coordinate
to be equal, including in characteristic two. -/
theorem matrix_eq_scalar_of_commutes_torus_short (A : Matrix (Index l) (Index l) K)
    (hT : ∀ (R : Type u) [CommRing R] [Algebra K R] (τ : ULift.{u} l → Rˣ),
      A.map (algebraMap K R) * Matrix.diagonal (fun i => (torusWeights τ i : R)) =
        Matrix.diagonal (fun i => (torusWeights τ i : R)) * A.map (algebraMap K R))
    (hS : ∀ a : l ⊕ l, A * shortMatrix a 1 = shortMatrix a 1 * A) :
    A = Matrix.diagonal (fun _ => A (Sum.inl ()) (Sum.inl ())) := by
  have hd := matrix_eq_diagonal_of_commutes_torus A hT
  have hall (i : Index l) : A i i = A (Sum.inl ()) (Sum.inl ()) := by
    rcases i with i | a
    · cases i; rfl
    · have h := congrFun (congrFun (hS a.swap) (Sum.inr a)) (Sum.inl ())
      rw [hd] at h
      have hentry : shortMatrix a.swap (1 : K) (Sum.inr a) (Sum.inl ()) = 1 := by
        simpa using shortMatrix_axis_entry a.swap (1 : K)
      simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, mul_one, one_mul] using h
  rw [hd]
  apply congrArg Matrix.diagonal
  exact funext hall

/-- A scalar odd quadratic isometry with determinant one is the identity.
The argument uses both defining equations and works over every coefficient ring. -/
theorem scalar_matrix_eq_one {R : Type u} [CommRing R] (f : K →+* R) (c : R)
    (hQ : OrthogonalMatrix.IsAlt
      (Matrix.diagonal (fun _ : Index l => c) * (formMatrix l K).map f *
        (Matrix.diagonal (fun _ : Index l => c)).transpose - (formMatrix l K).map f))
    (hdet : (Matrix.diagonal (fun _ : Index l => c)).det = 1) :
    Matrix.diagonal (fun _ : Index l => c) = 1 := by
  have hsq : c * c = 1 := by
    have h := ((OrthogonalMatrix.isAlt_iff _).mp hQ).2 (Sum.inl ())
    apply sub_eq_zero.mp
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, formMatrix] using h
  have hc : c = 1 := by
    rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_unique, Fintype.card_sum] at hdet
    have hpow : c ^ (Fintype.card l + Fintype.card l) = 1 := by
      rw [← two_mul, pow_mul, pow_two, hsq, one_pow]
    simpa only [pow_add, pow_one, hpow, mul_one] using hdet
  simp [hc]

/-- The torus and short families have trivial centralizer in the odd
norm-one matrix equations. -/
theorem matrix_eq_one_of_commutes_torus_short (A : Matrix (Index l) (Index l) K)
    (hT : ∀ (R : Type u) [CommRing R] [Algebra K R] (τ : ULift.{u} l → Rˣ),
      A.map (algebraMap K R) * Matrix.diagonal (fun i => (torusWeights τ i : R)) =
        Matrix.diagonal (fun i => (torusWeights τ i : R)) * A.map (algebraMap K R))
    (hS : ∀ a : l ⊕ l, A * shortMatrix a 1 = shortMatrix a 1 * A)
    (hQ : OrthogonalMatrix.IsAlt (A * formMatrix l K * A.transpose - formMatrix l K))
    (hdet : A.det = 1) : A = 1 := by
  have hscalar := matrix_eq_scalar_of_commutes_torus_short A hT hS
  rw [hscalar] at hQ hdet ⊢
  apply scalar_matrix_eq_one (RingHom.id K) _ _ hdet
  simpa using hQ

end Langlands.GroupScheme.OddOrthogonalMatrix
