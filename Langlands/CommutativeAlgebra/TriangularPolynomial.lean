import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Algebra.Equiv

/-! # Polynomial automorphisms from well-founded triangular substitutions -/

noncomputable section

universe u v

namespace Langlands.CommutativeAlgebra.TriangularPolynomial

open MvPolynomial

variable {R : Type u} [CommRing R] {ι : Type v}
    {rel : ι → ι → Prop}

/-- Each remainder involves only variables below its own index. -/
def HasLowerRemainders (rel : ι → ι → Prop) (f : ι → MvPolynomial ι R) : Prop :=
  ∀ i j, j ∈ (f i).vars → rel j i

/-- The polynomial substitution with unit diagonal and the supplied remainders. -/
def substitution (c : ι → Rˣ) (f : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  aeval fun i => C (c i : R) * X i + f i

/-- Well-founded recursive inverse coordinates. Values outside the lower set
are irrelevant to a lower remainder. -/
def inverseVariables (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) : ι → MvPolynomial ι R := by
  classical
  exact wf.fix fun i previous =>
    C (↑((c i)⁻¹) : R) *
      (X i - aeval (fun j => if h : rel j i then previous j h else X j) (f i))

private theorem aeval_eq_of_eq_on_vars (q : MvPolynomial ι R)
    (a b : ι → MvPolynomial ι R) (h : ∀ j ∈ q.vars, a j = b j) :
    aeval a q = aeval b q :=
  eval₂Hom_congr' rfl (fun j hj _ => h j hj) rfl

/-- The recursive inverse satisfies its triangular coordinate equation. -/
theorem inverseVariables_eq (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) (i : ι) :
    inverseVariables wf c f i =
      C (↑((c i)⁻¹) : R) *
        (X i - aeval (inverseVariables wf c f) (f i)) := by
  classical
  dsimp only [inverseVariables]
  rw [WellFounded.fix_eq]
  congr 2
  apply aeval_eq_of_eq_on_vars
  intro j hj
  simp only [hf i j hj, dite_true]

private theorem C_unit_mul_inv (c : Rˣ) :
    (C (c : R) : MvPolynomial ι R) * C (↑(c⁻¹) : R) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

private theorem C_inv_mul_unit (c : Rˣ) :
    (C (↑(c⁻¹) : R) : MvPolynomial ι R) * C (c : R) = 1 := by
  rw [mul_comm]
  exact C_unit_mul_inv c

/-- Substituting the recursive inverse after the original substitution is the identity. -/
theorem inverse_comp_substitution (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) :
    (aeval (inverseVariables wf c f)).comp (substitution c f) =
      AlgHom.id R (MvPolynomial ι R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitution, aeval_X, map_add, map_mul,
    aeval_C, algebraMap_eq, AlgHom.id_apply]
  rw [inverseVariables_eq wf c f hf, ← mul_assoc, C_unit_mul_inv,
    one_mul, sub_add_cancel]

/-- Substituting the original coordinates into each recursive inverse gives a variable. -/
theorem substitution_inverseVariables (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) :
    ∀ i, substitution c f (inverseVariables wf c f i) = X i := by
  intro i
  refine wf.induction
    (C := fun j => substitution c f (inverseVariables wf c f j) = X j) i ?_
  intro i ih
  have hrem : substitution c f (aeval (inverseVariables wf c f) (f i)) = f i := by
    rw [comp_aeval_apply]
    calc
      aeval (fun j => substitution c f (inverseVariables wf c f j)) (f i) =
          aeval X (f i) :=
        aeval_eq_of_eq_on_vars _ _ _ (fun j hj => ih j (hf i j hj))
      _ = f i := aeval_X_left_apply _
  rw [inverseVariables_eq wf c f hf, map_mul, map_sub, hrem]
  simp only [substitution, aeval_C, aeval_X, algebraMap_eq]
  rw [add_sub_cancel_right, ← mul_assoc, C_inv_mul_unit, one_mul]

/-- The recursive inverse is also a right inverse as an algebra homomorphism. -/
theorem substitution_comp_inverse (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) :
    (substitution c f).comp (aeval (inverseVariables wf c f)) =
      AlgHom.id R (MvPolynomial ι R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply] using
    substitution_inverseVariables wf c f hf i

/-- A triangular polynomial substitution with unit diagonal is an actual algebra
automorphism for every well-founded dependency relation. -/
def coordinateEquiv (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom (substitution c f) (aeval (inverseVariables wf c f))
    (substitution_comp_inverse wf c f hf) (inverse_comp_substitution wf c f hf)

theorem substitution_bijective (wf : WellFounded rel) (c : ι → Rˣ)
    (f : ι → MvPolynomial ι R) (hf : HasLowerRemainders rel f) :
    Function.Bijective (substitution c f) :=
  (coordinateEquiv wf c f hf).bijective

end Langlands.CommutativeAlgebra.TriangularPolynomial
