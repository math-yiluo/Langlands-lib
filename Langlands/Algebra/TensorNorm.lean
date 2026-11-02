import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Norms and arbitrary change of the tensor coefficient algebra -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.Algebra

variable {A B S T I : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]
  [Fintype I] [DecidableEq I]

/-- The multiplication matrix of a tensor commutes with any coefficient-algebra map. -/
theorem leftMulMatrix_tensor_map (b : Module.Basis I A B) (g : S →ₐ[A] T)
    (x : S ⊗[A] B) :
    Algebra.leftMulMatrix (b.baseChange T)
        (Algebra.TensorProduct.map g (AlgHom.id A B) x) =
      (Algebra.leftMulMatrix (b.baseChange S) x).map g := by
  ext i j
  induction x using TensorProduct.inductionOn with
  | tmul s y =>
      simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.smul_def]
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Finite-basis tensor norms are natural even for noninjective coefficient-algebra maps. -/
theorem norm_tensor_map_of_basis (b : Module.Basis I A B) (g : S →ₐ[A] T)
    (x : S ⊗[A] B) :
    Algebra.norm T (Algebra.TensorProduct.map g (AlgHom.id A B) x) =
      g (Algebra.norm S x) := by
  rw [Algebra.norm_eq_matrix_det (b.baseChange T),
    Algebra.norm_eq_matrix_det (b.baseChange S), g.map_det,
    leftMulMatrix_tensor_map b g x]
  rfl

variable (A B S)

/-- The determinant norm on `B ⊗ S`, using `S` as coefficient ring. -/
def tensorNorm : B ⊗[A] S →* S :=
  (Algebra.norm S).comp (Algebra.TensorProduct.comm A B S).toMonoidHom

@[simp] theorem tensorNorm_tmul (y : B) (s : S) :
    tensorNorm A B S (y ⊗ₜ s) = Algebra.norm S (s ⊗ₜ[A] y) := rfl

variable {A B S} [Module.Free A B] [Module.Finite A B]

/-- The tensor norm commutes with every change of coefficient algebra. -/
theorem tensorNorm_naturality (g : S →ₐ[A] T) (x : B ⊗[A] S) :
    tensorNorm A B T (Algebra.TensorProduct.lTensor (S := B) B g x) =
      g (tensorNorm A B S x) := by
  have h :
      (Algebra.TensorProduct.comm A B T).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := A) B g) =
        (Algebra.TensorProduct.map g (AlgHom.id A B)).comp
          (Algebra.TensorProduct.comm A B S).toAlgHom := by
    ext <;> simp
  change Algebra.norm T
      (((Algebra.TensorProduct.comm A B T).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := A) B g)) x) = _
  rw [h]
  exact norm_tensor_map_of_basis (Module.Free.chooseBasis A B) g _

/-- The norm of a scalar is its power by the rank of `B/A`. -/
theorem tensorNorm_scalar (s : S) :
    tensorNorm A B S (1 ⊗ₜ s) = s ^ Module.finrank A B := by
  nontriviality S
  have : Nontrivial A := Module.nontrivial A S
  rw [tensorNorm_tmul]
  change Algebra.norm S (algebraMap S (S ⊗[A] B) s) = _
  rw [Algebra.norm_algebraMap_of_basis ((Module.Free.chooseBasis A B).baseChange S)]
  congr 1
  exact (Module.finrank_eq_card_basis (Module.Free.chooseBasis A B)).symm

variable (A B S)

/-- The induced norm on units. -/
def tensorNormUnits : (B ⊗[A] S)ˣ →* Sˣ :=
  Units.map (tensorNorm A B S)

variable {A B S}

/-- Norms of units are natural for arbitrary coefficient-algebra maps. -/
theorem tensorNormUnits_naturality (g : S →ₐ[A] T) (x : (B ⊗[A] S)ˣ) :
    tensorNormUnits A B T
        (Units.map (Algebra.TensorProduct.lTensor (S := B) B g).toMonoidHom x) =
      Units.map g.toMonoidHom (tensorNormUnits A B S x) := by
  apply Units.ext
  exact tensorNorm_naturality g (x : B ⊗[A] S)

/-- The scalar-unit map followed by norm is the rank power map. -/
theorem tensorNormUnits_scalar (s : Sˣ) :
    tensorNormUnits A B S
        (Units.map (Algebra.TensorProduct.includeRight : S →ₐ[A] B ⊗[A] S).toMonoidHom s) =
      s ^ Module.finrank A B := by
  apply Units.ext
  exact tensorNorm_scalar (s : S)

end Langlands.Algebra
