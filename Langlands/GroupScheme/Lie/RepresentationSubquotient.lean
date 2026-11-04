import Langlands.GroupScheme.Lie.SemisimpleElement
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Semisimplicity and actual representation subquotients -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

section Endomorphisms

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  {a : Module.End R M} {b : Module.End R N}

/-- Semisimplicity passes to an injectively intertwined endomorphism. -/
theorem isSemisimple_of_injective_intertwiner (f : M →ₗ[R] N)
    (hf : Function.Injective f) (hcomm : f ∘ₗ a = b ∘ₗ f)
    (hb : b.IsSemisimple) : a.IsSemisimple := by
  let F : Module.AEval R M a →ₗ[R[X]] Module.AEval R N b :=
    LinearMap.ofAEval a ((Module.AEval.of R N b).toLinearMap ∘ₗ f)
      (fun x => by
        change (Module.AEval.of R N b) (f (a x)) =
          X • (Module.AEval.of R N b) (f x)
        rw [Module.AEval.X_smul_of]
        exact congrArg (Module.AEval.of R N b) (LinearMap.congr_fun hcomm x))
  let : IsSemisimpleModule R[X] (Module.AEval R N b) := hb
  exact IsSemisimpleModule.of_injective F hf

/-- Semisimplicity passes to a surjectively intertwined endomorphism. -/
theorem isSemisimple_of_surjective_intertwiner (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hcomm : f ∘ₗ a = b ∘ₗ f)
    (ha : a.IsSemisimple) : b.IsSemisimple := by
  let F : Module.AEval R M a →ₗ[R[X]] Module.AEval R N b :=
    LinearMap.ofAEval a ((Module.AEval.of R N b).toLinearMap ∘ₗ f)
      (fun x => by
        change (Module.AEval.of R N b) (f (a x)) =
          X • (Module.AEval.of R N b) (f x)
        rw [Module.AEval.X_smul_of]
        exact congrArg (Module.AEval.of R N b) (LinearMap.congr_fun hcomm x))
  let : IsSemisimpleModule R[X] (Module.AEval R M a) := ha
  exact IsSemisimpleModule.of_surjective F hf

end Endomorphisms

section Matrices

variable {k : Type u} [Field k]
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- An injective matrix stays injective after arbitrary scalar extension. -/
theorem mulVecLin_map_injective (C : Matrix m n k)
    (hC : Function.Injective C.mulVecLin)
    {A : Type*} [CommRing A] [Algebra k A] :
    Function.Injective (C.map (algebraMap k A)).mulVecLin := by
  obtain ⟨D, hD⟩ := C.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  have hDC : LinearMap.toMatrix' D * C = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact hD
  have hmap : (LinearMap.toMatrix' D).map (algebraMap k A) *
      C.map (algebraMap k A) = 1 := by
    rw [← Matrix.map_mul, hDC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hleft := congrArg Matrix.mulVecLin hmap
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] at hleft
  exact (show Function.LeftInverse
    ((LinearMap.toMatrix' D).map (algebraMap k A)).mulVecLin
    (C.map (algebraMap k A)).mulVecLin from
      fun x => LinearMap.congr_fun hleft x).injective

/-- A surjective matrix stays surjective after arbitrary scalar extension. -/
theorem mulVecLin_map_surjective (C : Matrix m n k)
    (hC : Function.Surjective C.mulVecLin)
    {A : Type*} [CommRing A] [Algebra k A] :
    Function.Surjective (C.map (algebraMap k A)).mulVecLin := by
  obtain ⟨D, hD⟩ := C.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hC)
  have hCD : C * LinearMap.toMatrix' D = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact hD
  have hmap : C.map (algebraMap k A) *
      (LinearMap.toMatrix' D).map (algebraMap k A) = 1 := by
    rw [← Matrix.map_mul, hCD]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hright := congrArg Matrix.mulVecLin hmap
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one] at hright
  exact (show Function.RightInverse
    ((LinearMap.toMatrix' D).map (algebraMap k A)).mulVecLin
    (C.map (algebraMap k A)).mulVecLin from
      fun x => LinearMap.congr_fun hright x).surjective

/-- Geometric semisimplicity passes through an injective matrix intertwiner. -/
theorem isGeometricallySemisimpleMatrix_of_injective_intertwiner
    {A : Matrix n n k} {B : Matrix m m k} (C : Matrix m n k)
    (hC : Function.Injective C.mulVecLin) (hcomm : C * A = B * C)
    (hB : IsGeometricallySemisimpleMatrix B) : IsGeometricallySemisimpleMatrix A := by
  apply isSemisimple_of_injective_intertwiner
    (C.map (algebraMap k (AlgebraicClosure k))).mulVecLin
    (mulVecLin_map_injective C hC)
    _ hB
  have h := congrArg (fun M => M.map (algebraMap k (AlgebraicClosure k))) hcomm
  simpa only [Matrix.map_mul, Matrix.toLin'_apply',
    Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin h

/-- Geometric semisimplicity passes through a surjective matrix intertwiner. -/
theorem isGeometricallySemisimpleMatrix_of_surjective_intertwiner
    {A : Matrix n n k} {B : Matrix m m k} (C : Matrix m n k)
    (hC : Function.Surjective C.mulVecLin) (hcomm : C * A = B * C)
    (hA : IsGeometricallySemisimpleMatrix A) : IsGeometricallySemisimpleMatrix B := by
  apply isSemisimple_of_surjective_intertwiner
    (C.map (algebraMap k (AlgebraicClosure k))).mulVecLin
    (mulVecLin_map_surjective C hC)
    _ hA
  have h := congrArg (fun M => M.map (algebraMap k (AlgebraicClosure k))) hcomm
  simpa only [Matrix.map_mul, Matrix.toLin'_apply',
    Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin h

end Matrices

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A constant matrix intertwines two actual representations when its scalar
extension intertwines their actions on every affine scheme test. -/
def Intertwines (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (C : Matrix m n k) : Prop :=
  ∀ (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X),
    C.map (algebraMap k S) * (ρ.affineMatrix S x : Matrix n n S) =
      (σ.affineMatrix S x : Matrix m m S) * C.map (algebraMap k S)

/-- Differentiating an actual intertwiner is extraction of its epsilon coefficient. -/
theorem Intertwines.tangentMatrix {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : Intertwines ρ σ C) (X : lieKernel G k) :
    C * ρ.tangentMatrix k X = σ.tangentMatrix k X * C := by
  have h := hC (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun M => (M i j).snd) h
  change (C * Matrix.of (fun i j =>
    ((ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val :
      Matrix n n (DualNumber k)) i j).snd)) i j =
    (Matrix.of (fun i j =>
    ((σ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val :
      Matrix m m (DualNumber k)) i j).snd) * C) i j
  simpa [Matrix.mul_apply, Matrix.map_apply, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.snd_sum] using hij

/-- A finite dimensional actual representation is a subquotient of another when
an intermediate actual representation embeds in the latter and surjects onto it. -/
def IsSubquotientOf {n m : ℕ} (σ : MatrixRepresentation G (Fin n))
    (ρ : MatrixRepresentation G (Fin m)) : Prop :=
  ∃ (r : ℕ) (τ : MatrixRepresentation G (Fin r))
    (C : Matrix (Fin m) (Fin r) k) (D : Matrix (Fin n) (Fin r) k),
    Intertwines τ ρ C ∧ Function.Injective C.mulVecLin ∧
    Intertwines τ σ D ∧ Function.Surjective D.mulVecLin

/-- A representation subquotient inherits a geometrically semisimple differential. -/
theorem IsSubquotientOf.isGeometricallySemisimpleMatrix {n m : ℕ}
    {σ : MatrixRepresentation G (Fin n)} {ρ : MatrixRepresentation G (Fin m)}
    (h : IsSubquotientOf σ ρ) (X : lieKernel G k)
    (hρ : Lie.IsGeometricallySemisimpleMatrix (ρ.tangentMatrix k X)) :
    Lie.IsGeometricallySemisimpleMatrix (σ.tangentMatrix k X) := by
  obtain ⟨r, τ, C, D, hC, hi, hD, hs⟩ := h
  exact Lie.isGeometricallySemisimpleMatrix_of_surjective_intertwiner D hs
    (hD.tangentMatrix X)
    (Lie.isGeometricallySemisimpleMatrix_of_injective_intertwiner C hi
      (hC.tangentMatrix X) hρ)

/-- If all source representations are subquotients of restricted target
representations, representation-tested semisimplicity reflects along the map. -/
theorem isSemisimpleElement_of_subquotients (f : H ⟶ G)
    (hsub : ∀ (n : ℕ) (σ : MatrixRepresentation H (Fin n)),
      ∃ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
        IsSubquotientOf σ (ρ.restrict f))
    {X : lieKernel H k} (hX : Lie.IsSemisimpleElement G (Lie.targetMap f k X)) :
    Lie.IsSemisimpleElement H X := by
  intro n σ
  obtain ⟨m, ρ, hσ⟩ := hsub n σ
  apply hσ.isGeometricallySemisimpleMatrix X
  rw [tangentMatrix_restrict]
  exact hX m ρ

end Langlands.GroupScheme.MatrixRepresentation
