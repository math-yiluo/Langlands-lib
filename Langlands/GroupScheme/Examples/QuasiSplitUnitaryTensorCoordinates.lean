import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {I : Type u} (v : Module.Basis I F E)
variable (R : Type u) [CommRing R] [Algebra F R]

/-- Scalar coordinates of a tensor, with respect to a basis of the extension. -/
def tensorCoeff : E ⊗[F] R →ₗ[R] (I →₀ R) :=
  (v.baseChange R).repr.toLinearMap.comp (Algebra.TensorProduct.commRight F R E).symm.toLinearMap

@[simp] theorem tensorCoeff_tmul (e : E) (r : R) (k : I) :
    tensorCoeff v R (e ⊗ₜ[F] r) k = algebraMap F R (v.repr e k) * r := by
  simp [tensorCoeff, Algebra.smul_def]

theorem tensorCoeff_injective : Function.Injective (tensorCoeff v R) :=
  (v.baseChange R).repr.injective.comp (Algebra.TensorProduct.commRight F R E).symm.injective

@[simp] theorem tensorCoeff_scalar_mul (r : R) (x : E ⊗[F] R) (k : I) :
    tensorCoeff v R (algebraMap R (E ⊗[F] R) r * x) k =
      r * tensorCoeff v R x k := by
  rw [← Algebra.smul_def, map_smul]
  rfl

@[simp] theorem tensorCoeff_mul_scalar (r : R) (x : E ⊗[F] R) (k : I) :
    tensorCoeff v R (x * algebraMap R (E ⊗[F] R) r) k =
      tensorCoeff v R x k * r := by
  rw [mul_comm, tensorCoeff_scalar_mul, mul_comm]

variable {R} {S : Type u} [CommRing S] [Algebra F S]

theorem tensorCoeff_naturality (f : R →ₐ[F] S) (x : E ⊗[F] R) (k : I) :
    tensorCoeff v S (tensorCoefficientMap f x) k = f (tensorCoeff v R x k) := by
  induction x using TensorProduct.inductionOn with
  | tmul e r => simp
  | add x y hx hy => simp [hx, hy]

variable [IsQuadraticExtension F E]
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- Each scalar coordinate of each matrix entry is a global function. -/
def entryCoeff (T : Over (Spec (CommRingCat.of F)))
    (g : T ⟶ (groupScheme b c).X) (i j : Fin 2) (k : I) : Γ(T.left, ⊤) :=
  tensorCoeff v ((algΓ (CommRingCat.of F)).obj T).unop (matrixCoordinates b c T g i j) k

theorem entryCoeff_comp {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (g : T ⟶ (groupScheme b c).X) (i j : Fin 2) (k : I) :
    entryCoeff v b c T' (a ≫ g) i j k = a.left.appTop (entryCoeff v b c T g i j k) := by
  unfold entryCoeff
  rw [matrixCoordinates_naturality]
  exact tensorCoeff_naturality v ((algΓ (CommRingCat.of F)).map a).unop.hom _ _

end Langlands.GroupScheme.QuasiSplitUnitary
