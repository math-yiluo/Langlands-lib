import Langlands.GroupScheme.Reductive.RegularConjugationReduction
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Conjugation maps from actual tensor-dual intertwiners -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixLinear

variable {k : Type u} [CommRing k]
  {n m : Type} [Fintype n]

/-- Reshape the output coordinates of a rectangular linear map into matrices. -/
def tensorCoefficients (C : Matrix (m × m) n k) : n → Matrix m m k :=
  fun a i j => C (i, j) a

/-- The reshaped map evaluates to the original vector, with a pair of indices. -/
theorem eval_tensorCoefficients (C : Matrix (m × m) n k)
    {A : Type*} [CommRing A] (f : k →+* A) (x : n → A) (i j : m) :
    eval (tensorCoefficients C) f x i j = (C.map f *ᵥ x) (i, j) := rfl

/-- Reshaping preserves the nonvanishing of the linear image. -/
theorem eval_tensorCoefficients_ne_zero_iff (C : Matrix (m × m) n k) (v : n → k) :
    eval (tensorCoefficients C) (RingHom.id k) v ≠ 0 ↔ C *ᵥ v ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    ext i j
    exact congrFun hzero (i, j)
  · intro h hzero
    apply h
    funext p
    exact congrFun (congrFun hzero p.1) p.2

end MatrixLinear

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- On every scheme test, row-first tensor-dual coordinates are conjugation
coordinates on matrices. -/
theorem tensor_dual_pointMatrix_mulVec (σ : MatrixRepresentation G m)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (x : m × m → Γ(T.left, ⊤)) (i j : m) :
    (((σ.tensor σ.dual).pointMatrix T g : Matrix (m × m) (m × m) Γ(T.left, ⊤)) *ᵥ x)
        (i, j) =
      ((σ.pointMatrix T g : Matrix m m Γ(T.left, ⊤)) *
        (Matrix.of fun a b => x (a, b)) * ((σ.pointMatrix T g)⁻¹).val) i j := by
  simp only [Matrix.mulVec, dotProduct, tensor_pointMatrix_entry, dual_pointMatrix,
    GeneralLinear.matrixContragredient_coe, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by ring

namespace ConjugationLinearMap

variable [IsAffine G.X.left] {ρ : MatrixRepresentation G n}
  {σ : MatrixRepresentation G m}

/-- An actual intertwiner into the tensor with the dual gives a conjugation map
on every scheme test. -/
def ofTensorIntertwiner {C : Matrix (m × m) n k}
    (hC : Intertwines ρ (σ.tensor σ.dual) C) : ConjugationLinearMap ρ σ where
  coeff := MatrixLinear.tensorCoefficients C
  equivariant T g x := by
    ext i j
    rw [MatrixLinear.eval_tensorCoefficients, Matrix.mulVec_mulVec,
      hC.points T g, ← Matrix.mulVec_mulVec]
    exact tensor_dual_pointMatrix_mulVec σ T g _ i j

/-- The constructed matrix at a base-field vector has exactly the tensor image
as its row-first entries. -/
theorem ofTensorIntertwiner_eval {C : Matrix (m × m) n k}
    (hC : Intertwines ρ (σ.tensor σ.dual) C) (v : n → k) (i j : m) :
    MatrixLinear.eval (ofTensorIntertwiner hC).coeff (RingHom.id k) v i j =
      (C *ᵥ v) (i, j) := rfl

/-- A nonzero tensor image gives a nonzero matrix under the constructed map. -/
theorem ofTensorIntertwiner_eval_ne_zero_iff {C : Matrix (m × m) n k}
    (hC : Intertwines ρ (σ.tensor σ.dual) C) (v : n → k) :
    MatrixLinear.eval (ofTensorIntertwiner hC).coeff (RingHom.id k) v ≠ 0 ↔
      C *ᵥ v ≠ 0 :=
  MatrixLinear.eval_tensorCoefficients_ne_zero_iff C v

end ConjugationLinearMap
end MatrixRepresentation
end Langlands.GroupScheme
