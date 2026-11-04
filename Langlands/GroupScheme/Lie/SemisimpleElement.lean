import Langlands.GroupScheme.Lie.RepresentationDifferential
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Semisimple

/-! # Geometric semisimplicity of actual Lie elements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A matrix is geometrically semisimple when the resulting endomorphism
after extension to the algebraic closure is semisimple. -/
def IsGeometricallySemisimpleMatrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n k) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))))

@[simp] theorem isGeometricallySemisimpleMatrix_zero {n : Type}
    [Fintype n] [DecidableEq n] :
    IsGeometricallySemisimpleMatrix (0 : Matrix n n k) := by
  unfold IsGeometricallySemisimpleMatrix
  simp only [Matrix.map_zero _ (map_zero _), map_zero, Module.End.isSemisimple_zero]

/-- Epsilon scaling preserves geometric semisimplicity, including the zero scalar. -/
theorem IsGeometricallySemisimpleMatrix.smul {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n k} (hM : IsGeometricallySemisimpleMatrix M) (c : k) :
    IsGeometricallySemisimpleMatrix (c • M) := by
  unfold IsGeometricallySemisimpleMatrix at hM ⊢
  have h : (c • M).map (algebraMap k (AlgebraicClosure k)) =
      algebraMap k (AlgebraicClosure k) c • M.map (algebraMap k (AlgebraicClosure k)) := by
    ext i j
    change algebraMap k (AlgebraicClosure k) (c * M i j) =
      algebraMap k (AlgebraicClosure k) c * algebraMap k (AlgebraicClosure k) (M i j)
    exact (algebraMap k (AlgebraicClosure k)).map_mul c (M i j)
  rw [h, map_smul]
  exact Module.End.IsSemisimple_smul _ hM

/-- An actual Lie element is semisimple if every finite dimensional algebraic
group representation has a geometrically semisimple differential at that element.
The representations are genuine group-scheme homomorphisms. -/
def IsSemisimpleElement (G : GroupScheme (Spec (CommRingCat.of k)))
    (X : lieKernel G k) : Prop :=
  ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
    IsGeometricallySemisimpleMatrix (ρ.tangentMatrix k X)

/-- The zero tangent vector, written as the identity of the raw kernel, is semisimple. -/
@[simp] theorem isSemisimpleElement_one : IsSemisimpleElement G (1 : lieKernel G k) := by
  intro n ρ
  rw [MatrixRepresentation.tangentMatrix_one]
  exact isGeometricallySemisimpleMatrix_zero

/-- Semisimplicity is preserved by the actual epsilon-scaling operation. -/
theorem IsSemisimpleElement.scale {X : lieKernel G k}
    (hX : IsSemisimpleElement G X) (c : k) :
    IsSemisimpleElement G (lieKernelScale G c X) := by
  intro n ρ
  rw [MatrixRepresentation.tangentMatrix_scale]
  exact (hX n ρ).smul c

/-- Homomorphisms preserve representation-tested geometric semisimplicity. -/
theorem IsSemisimpleElement.map {X : lieKernel G k}
    (hX : IsSemisimpleElement G X) (f : G ⟶ H) :
    IsSemisimpleElement H (targetMap f k X) := by
  intro n ρ
  rw [← MatrixRepresentation.tangentMatrix_restrict]
  exact hX n (ρ.restrict f)

end Langlands.GroupScheme.Lie
