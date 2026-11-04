import Langlands.GroupScheme.Rational.TorusGrading
import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Homogeneous primitive generators for split-torus actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A coordinate function is primitive when it is additive on every algebra's points. -/
def IsPrimitiveFunction (f : B) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (x y : F.obj A),
    coord e (x * y) f = coord e x f + coord e y f

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- Taking a torus weight component preserves primitivity. -/
theorem isPrimitiveFunction_comp {f : B} (hf : IsPrimitiveFunction e f) (m : I → ℤ) :
    IsPrimitiveFunction e (comp e σ m f) := by
  intro A x y
  have h := congrArg (fun p : AddMonoidAlgebra A (I → ℤ) => p.coeff m)
    (hf (laurent I A) (hat σ x) (hat σ y))
  rw [← map_mul, coord_hat_coeff, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, coord_hat_coeff, coord_hat_coeff] at h
  exact h

/-- A finite primitive generating family can be replaced by a finite homogeneous one.
The new family consists of the components in the original generators' coaction supports. -/
theorem exists_homogeneous_primitive_generators {n : ℕ} (x : Fin n → B)
    (hx : VectorGroup.IsPrimitiveFamily e x)
    (hgen : Function.Surjective (aeval x : MvPolynomial (Fin n) R →ₐ[R] B)) :
    ∃ (N : ℕ) (y : Fin N → B) (w : Fin N → I → ℤ),
      VectorGroup.IsPrimitiveFamily e y ∧
      (∀ i, IsHomogeneous e σ (w i) (y i)) ∧
      Function.Surjective (aeval y : MvPolynomial (Fin N) R →ₐ[R] B) := by
  classical
  let J := Σ i : Fin n, ↥((rho e σ (x i)).coeff.support)
  let y : J → B := fun j => comp e σ j.2 (x j.1)
  have hy : Function.Surjective (aeval y : MvPolynomial J R →ₐ[R] B) := by
    have hle : Algebra.adjoin R (Set.range x) ≤ (aeval y : MvPolynomial J R →ₐ[R] B).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      rw [← sum_support_comp e σ (x i)]
      apply Subalgebra.sum_mem
      intro m hm
      exact ⟨X ⟨i, ⟨m, hm⟩⟩, aeval_X y _⟩
    intro b
    obtain ⟨p, rfl⟩ := hgen b
    apply hle
    rw [← aeval_range]
    exact ⟨p, rfl⟩
  let N := Fintype.card J
  let q : Fin N ≃ J := (Fintype.equivFin J).symm
  refine ⟨N, y ∘ q, fun i => (q i).2, ?_, ?_, ?_⟩
  · intro A a b i
    exact isPrimitiveFunction_comp e σ (fun A a b => hx A a b (q i).1) (q i).2 A a b
  · intro i
    exact isHomogeneous_comp e σ (q i).2 (x (q i).1)
  · intro b
    obtain ⟨p, hp⟩ := hy b
    refine ⟨rename q.symm p, ?_⟩
    rw [aeval_rename]
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hp

/-- A primitive generating family defines a closed immersion into a vector group. -/
theorem isClosedImmersion_quotientMap {n : ℕ} {y : Fin n → B}
    (hy : VectorGroup.IsPrimitiveFamily e y)
    (hgen : Function.Surjective (aeval y : MvPolynomial (Fin n) R →ₐ[R] B)) :
    IsClosedImmersion (VectorGroup.quotientMap hy).hom.hom.left := by
  rw [VectorGroup.quotientMap_left]
  exact IsClosedImmersion.spec_of_surjective _ hgen

/-- The additive embedding supplied by homogeneous primitive generators is diagonal
on algebra-valued points. -/
theorem coordinateMap_act_of_isHomogeneous {n : ℕ} {y : Fin n → B}
    (hy : VectorGroup.IsPrimitiveFamily e y) (w : Fin n → I → ℤ)
    (hw : ∀ i, IsHomogeneous e σ (w i) (y i))
    {A : CommAlgCat.{u} R} (t : I → Aˣ) (x : F.obj A) (i : Fin n) :
    ((VectorGroup.coordinateMap hy).app A (σ.act t x)).toAdd i =
      ((VectorGroup.coordinateMap hy).app A x).toAdd i *
        (splitTorus.exponentValue I t (Multiplicative.ofAdd (w i)) : A) := by
  exact coord_act_of_isHomogeneous e σ t x (hw i)

end Langlands.GroupScheme.Corepresented
