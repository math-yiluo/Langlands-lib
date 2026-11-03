import Langlands.AlgebraicGeometry.FiniteLinearEquationsScheme
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Finite linear equations for kernels after tensoring finite free modules -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.FiniteLinearEquations.TensorKernel

variable {R : Type u} [CommRing R]
  {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  {m n : ℕ}

/-- The coordinates of a tensor with a finite free module. -/
def coordinates (e : P ≃ₗ[R] (Fin n → R))
    (A : Type v) [AddCommGroup A] [Module R A] :
    A ⊗[R] P ≃ₗ[R] (Fin n → A) :=
  TensorProduct.congr (LinearEquiv.refl R A) e ≪≫ₗ
    TensorProduct.piScalarRight R R A (Fin n)

@[simp]
lemma coordinates_tmul (e : P ≃ₗ[R] (Fin n → R))
    {A : Type v} [AddCommGroup A] [Module R A] (x : A) (p : P) (i : Fin n) :
    coordinates e A (x ⊗ₜ[R] p) i = e p i • x := by
  simp [coordinates]

/-- The matrix of an actual module map in the two chosen coordinate systems. -/
def matrix (f : P →ₗ[R] Q) (eP : P ≃ₗ[R] (Fin n → R))
    (eQ : Q ≃ₗ[R] (Fin m → R)) : Fin m → Fin n → R :=
  LinearMap.toMatrix' (eQ.toLinearMap.comp (f.comp eP.symm.toLinearMap))

lemma matrix_mul_coordinates (f : P →ₗ[R] Q)
    (eP : P ≃ₗ[R] (Fin n → R)) (eQ : Q ≃ₗ[R] (Fin m → R))
    (p : P) (j : Fin m) :
    ∑ i, matrix f eP eQ j i * eP p i = eQ (f p) j := by
  simpa [matrix, Matrix.mulVec, dotProduct] using
    congrFun (LinearMap.toMatrix'_mulVec
      (eQ.toLinearMap.comp (f.comp eP.symm.toLinearMap)) (eP p)) j

lemma coordinates_map (f : P →ₗ[R] Q)
    (eP : P ≃ₗ[R] (Fin n → R)) (eQ : Q ≃ₗ[R] (Fin m → R))
    {A : Type v} [AddCommGroup A] [Module R A] (z : A ⊗[R] P) (j : Fin m) :
    coordinates eQ A (TensorProduct.map (LinearMap.id : A →ₗ[R] A) f z) j =
      ∑ i, matrix f eP eQ j i • coordinates eP A z i := by
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, coordinates_tmul]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, matrix_mul_coordinates]
  | add z z' hz hz' =>
      simp only [map_add, Pi.add_apply, hz, hz', smul_add, Finset.sum_add_distrib]

lemma coordinates_map_left (eP : P ≃ₗ[R] (Fin n → R))
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (q : A →ₗ[R] B) (z : A ⊗[R] P) (i : Fin n) :
    coordinates eP B (TensorProduct.map q (LinearMap.id : P →ₗ[R] P) z) i =
      q (coordinates eP A z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul x p => simp
  | add z z' hz hz' => simp only [map_add, Pi.add_apply, hz, hz']

/-- A coefficient-linear map acts on the actual tensor kernels. -/
def mapKernel (f : P →ₗ[R] Q)
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B] (q : A →ₗ[R] B) :
    (TensorProduct.map (LinearMap.id : A →ₗ[R] A) f).ker →
      (TensorProduct.map (LinearMap.id : B →ₗ[R] B) f).ker :=
  fun z ↦ ⟨TensorProduct.map q LinearMap.id z.val, by
    have hcomm :
        (TensorProduct.map (LinearMap.id : B →ₗ[R] B) f).comp
            (TensorProduct.map q (LinearMap.id : P →ₗ[R] P)) =
          (TensorProduct.map q (LinearMap.id : Q →ₗ[R] Q)).comp
            (TensorProduct.map (LinearMap.id : A →ₗ[R] A) f) := by
      ext x p
      simp
    change _ = 0
    rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, z.property, map_zero]⟩

/-- The actual tensor kernel equals the solutions of the coordinate matrix. -/
def kernelEquiv (f : P →ₗ[R] Q)
    (eP : P ≃ₗ[R] (Fin n → R)) (eQ : Q ≃ₗ[R] (Fin m → R))
    (S : Type v) [CommRing S] [Algebra R S] :
    (TensorProduct.map (LinearMap.id : S →ₗ[R] S) f).ker ≃
      Solutions (matrix f eP eQ) S where
  toFun z := ⟨coordinates eP S z.val, fun j ↦ by
    have h := coordinates_map f eP eQ z.val j
    rw [z.property, map_zero, Pi.zero_apply] at h
    simpa only [Algebra.smul_def] using h.symm⟩
  invFun x := ⟨(coordinates eP S).symm x.val, by
    apply (coordinates eQ S).injective
    ext j
    rw [coordinates_map f eP eQ, LinearEquiv.apply_symm_apply]
    simpa only [map_zero, Pi.zero_apply, Algebra.smul_def] using x.property j⟩
  left_inv z := Subtype.ext ((coordinates eP S).symm_apply_apply z.val)
  right_inv x := Subtype.ext ((coordinates eP S).apply_symm_apply x.val)

/-- Kernel coordinates commute with every scalar-compatible coefficient map. -/
lemma kernelEquiv_naturality (f : P →ₗ[R] Q)
    (eP : P ≃ₗ[R] (Fin n → R)) (eQ : Q ≃ₗ[R] (Fin m → R))
    {S : Type v} [CommRing S] [Algebra R S]
    {S' : Type w} [CommRing S'] [Algebra R S']
    (q : S →ₐ[R] S') (z : (TensorProduct.map (LinearMap.id : S →ₗ[R] S) f).ker) :
    kernelEquiv f eP eQ S' (mapKernel f q.toLinearMap z) =
      mapSolutions (matrix f eP eQ) q (kernelEquiv f eP eQ S z) := by
  apply Subtype.ext
  funext i
  exact coordinates_map_left eP q.toLinearMap z.val i

end Langlands.AlgebraicGeometry.FiniteLinearEquations.TensorKernel
