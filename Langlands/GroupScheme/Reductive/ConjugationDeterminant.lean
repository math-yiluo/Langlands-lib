import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Invariant polynomials from linear maps into conjugation representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

namespace MatrixLinear

variable {k : Type u} [CommRing k]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Evaluate the linear matrix with coefficient matrices `c` after a change of scalars. -/
def eval (c : n → Matrix m m k) {A : Type*} [CommRing A] (f : k →+* A)
    (x : n → A) : Matrix m m A :=
  fun i j => ∑ a, f (c a i j) * x a

/-- The matrix of linear coordinate polynomials with coefficient matrices `c`. -/
def polynomial (c : n → Matrix m m k) : Matrix m m (MvPolynomial n k) :=
  fun i j => ∑ a, MvPolynomial.C (c a i j) * MvPolynomial.X a

/-- The determinant polynomial of a linear matrix. -/
def determinant (c : n → Matrix m m k) : MvPolynomial n k :=
  (polynomial c).det

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem polynomial_isHomogeneous (c : n → Matrix m m k) (i j : m) :
    (polynomial c i j).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

omit [DecidableEq n] in
theorem determinant_isHomogeneous (c : n → Matrix m m k) :
    (determinant c).IsHomogeneous (Fintype.card m) := by
  classical
  unfold determinant
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro s _
  have hp : (∏ i, polynomial c (s i) i).IsHomogeneous (Fintype.card m) := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => polynomial c (s i) i) (fun _ => 1)
      (fun i _ => polynomial_isHomogeneous c (s i) i)
  simpa using hp.C_mul (s.sign : k)

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem eval_polynomial (c : n → Matrix m m k) {A : Type*} [CommRing A]
    (f : k →+* A) (x : n → A) :
    (polynomial c).map (MvPolynomial.eval₂Hom f x) = eval c f x := by
  ext i j
  simp [polynomial, eval]

omit [DecidableEq n] in
theorem eval_determinant (c : n → Matrix m m k) {A : Type*} [CommRing A]
    (f : k →+* A) (x : n → A) :
    MvPolynomial.eval₂ f x (determinant c) = (eval c f x).det := by
  change (MvPolynomial.eval₂Hom f x) (polynomial c).det = _
  rw [RingHom.map_det]
  change ((polynomial c).map (MvPolynomial.eval₂Hom f x)).det = _
  rw [eval_polynomial]

end MatrixLinear

namespace MatrixRepresentation

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A linear map to matrices intertwining the given action with conjugation by an
actual coefficient representation, on every test scheme. -/
structure ConjugationLinearMap (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) where
  coeff : n → Matrix m m k
  equivariant :
    ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
      MatrixLinear.eval coeff (scalarMap T)
          ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) =
        (σ.pointMatrix T g : Matrix m m Γ(T.left, ⊤)) *
          MatrixLinear.eval coeff (scalarMap T) x *
          ((σ.pointMatrix T g)⁻¹).val

namespace ConjugationLinearMap

variable {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}

/-- A conjugation-equivariant linear matrix, invertible at `v`, yields an invariant
homogeneous polynomial of positive degree if the target matrix size is nonzero. -/
theorem exists_invariant_polynomial [Nonempty m] (φ : ConjugationLinearMap ρ σ)
    (v : n → k) (hv : (MatrixLinear.eval φ.coeff (RingHom.id k) v).det ≠ 0) :
    ∃ (d : ℕ) (F : MvPolynomial n k), 0 < d ∧ F.IsHomogeneous d ∧
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
        MvPolynomial.eval₂ (scalarMap T)
            ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
          MvPolynomial.eval₂ (scalarMap T) x F) ∧
      MvPolynomial.eval v F ≠ 0 := by
  refine ⟨Fintype.card m, MatrixLinear.determinant φ.coeff, Fintype.card_pos,
    MatrixLinear.determinant_isHomogeneous _, ?_, ?_⟩
  · intro T g x
    rw [MatrixLinear.eval_determinant, MatrixLinear.eval_determinant, φ.equivariant]
    exact Matrix.det_units_conj (σ.pointMatrix T g) _
  · exact (MatrixLinear.eval_determinant φ.coeff (RingHom.id k) v).trans_ne hv

end ConjugationLinearMap
end MatrixRepresentation
end Langlands.GroupScheme
