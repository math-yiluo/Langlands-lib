import Langlands.Geometry.Manifold.SmoothGroupLieDifferential
import Langlands.Geometry.Manifold.VectorFieldCommutator
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Matrix.Mul

/-! # The differential of a smooth matrix representation preserves brackets

Let `G` be a real Lie group and `φ : G →* Matrix N N 𝕜` a monoid homomorphism into square
matrices over a real normed algebra `𝕜`, all of whose entries are smooth. Its differential at the
identity, computed entrywise, sends Mathlib's bracket on `GroupLieAlgebra` to the matrix
commutator.
-/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold.MatrixCoefficientLie

open Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Post-composition with a continuous linear map commutes with the manifold derivative of a
vector-valued function. -/
theorem mvfderiv_clm_comp {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {Φ : M → F} {x : M}
    (hΦ : MDifferentiableAt I 𝓘(ℝ, F) Φ x) (L : F →L[ℝ] F') (v : TangentSpace I x) :
    mvfderiv I (fun g => L (Φ g)) x v = L (mvfderiv I Φ x v) := by
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ, F)) (I' := I) (g := (L : F → F')) (f := Φ) x
    ((L.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)) hΦ v
  rw [show (fun g => L (Φ g)) = (L : F → F') ∘ Φ from rfl, h, mvfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv]
  rfl

variable {𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]
  {N : Type*} [Fintype N]

/-- The entries of a matrix-valued map, as a map into a normed space. -/
def entryMap (φ : M → Matrix N N 𝕜) : M → (N → N → 𝕜) := fun g a b => φ g a b

/-- The entrywise derivative of a matrix-valued map. -/
def entryDerivative (φ : M → Matrix N N 𝕜) (x : M) (v : TangentSpace I x) : Matrix N N 𝕜 :=
  Matrix.of fun a b => mvfderiv I (fun g => φ g a b) x v

theorem contMDiff_entryMap {φ : M → Matrix N N 𝕜}
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b)) :
    ContMDiff I 𝓘(ℝ, N → N → 𝕜) ∞ (entryMap φ) :=
  contMDiff_pi_space.2 fun a => contMDiff_pi_space.2 fun b => hφ a b

/-- The `(a, b)` entry, as a continuous linear map. -/
def entryCLM (a b : N) : (N → N → 𝕜) →L[ℝ] 𝕜 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => 𝕜) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => N → 𝕜) a)

omit [Fintype N] in
@[simp] theorem entryCLM_apply (a b : N) (m : N → N → 𝕜) : entryCLM a b m = m a b := rfl

theorem mvfderiv_entryMap {φ : M → Matrix N N 𝕜}
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b)) (x : M) (v : TangentSpace I x) :
    Matrix.of (mvfderiv I (entryMap φ) x v) = entryDerivative I φ x v := by
  ext a b
  have hproj := mvfderiv_clm_comp I
    ((contMDiff_entryMap I hφ).mdifferentiableAt (by simp) (x := x)) (entryCLM a b) v
  simp only [entryCLM_apply] at hproj
  simp only [Matrix.of_apply, entryDerivative]
  exact hproj.symm

/-- The continuous real-linear functional `M ↦ ℓ ((P * M * Q) i j)` on matrices. -/
def testFunctional (P Q : Matrix N N 𝕜) (ℓ : 𝕜 →L[ℝ] ℝ) (i j : N) :
    (N → N → 𝕜) →L[ℝ] ℂ :=
  ∑ a, ∑ b, Complex.ofRealCLM.comp
    (ℓ.comp ((ContinuousLinearMap.mulLeftRight ℝ 𝕜 (P i a) (Q b j)).comp (entryCLM a b)))

theorem testFunctional_apply (P Q : Matrix N N 𝕜) (ℓ : 𝕜 →L[ℝ] ℝ) (i j : N)
    (m : N → N → 𝕜) :
    testFunctional P Q ℓ i j m = (ℓ ((P * Matrix.of m * Q) i j) : ℂ) := by
  simp only [testFunctional, sum_apply, ContinuousLinearMap.comp_apply,
    entryCLM_apply, ContinuousLinearMap.mulLeftRight_apply, Complex.ofRealCLM_apply,
    Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, map_sum, Complex.ofReal_sum]
  rw [Finset.sum_comm]

variable {I} in
/-- The derivative of a test function of the entries. -/
theorem mvfderiv_test {φ : M → Matrix N N 𝕜}
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b))
    (P Q : Matrix N N 𝕜) (ℓ : 𝕜 →L[ℝ] ℝ) (i j : N) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun g => (ℓ ((P * φ g * Q) i j) : ℂ)) x v =
      (ℓ ((P * entryDerivative I φ x v * Q) i j) : ℂ) := by
  have hE := contMDiff_entryMap I hφ
  have hfun : (fun g => (ℓ ((P * φ g * Q) i j) : ℂ)) =
      fun g => testFunctional P Q ℓ i j (entryMap φ g) := by
    funext g
    rw [testFunctional_apply]
    rfl
  rw [hfun, mvfderiv_clm_comp I (hE.mdifferentiableAt (by simp)), testFunctional_apply,
    mvfderiv_entryMap I hφ]

variable {I} in
theorem contMDiff_test {φ : M → Matrix N N 𝕜}
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b))
    (P Q : Matrix N N 𝕜) (ℓ : 𝕜 →L[ℝ] ℝ) (i j : N) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => (ℓ ((P * φ g * Q) i j) : ℂ)) := by
  have hfun : (fun g => (ℓ ((P * φ g * Q) i j) : ℂ)) =
      fun g => testFunctional P Q ℓ i j (entryMap φ g) := by
    funext g
    rw [testFunctional_apply]
    rfl
  rw [hfun]
  exact (testFunctional P Q ℓ i j).contDiff.contMDiff.comp (contMDiff_entryMap I hφ)

variable [DecidableEq N]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The differential at the identity of a matrix representation, entrywise. -/
def matrixDifferential (φ : G →* Matrix N N 𝕜) :
    GroupLieAlgebra I G →ₗ[ℝ] Matrix N N 𝕜 where
  toFun X := entryDerivative I (fun g => φ g) 1 X
  map_add' X Y := by
    ext a b
    simp [entryDerivative]
  map_smul' c X := by
    ext a b
    simp [entryDerivative]

omit [LieGroup I ∞ G] in
theorem matrixDifferential_apply (φ : G →* Matrix N N 𝕜) (X : GroupLieAlgebra I G) (a b : N) :
    matrixDifferential I φ X a b = mvfderiv I (fun g => φ g a b) 1 X := rfl


variable {I}

omit [LieGroup I ∞ G] in
/-- Directional differentiation of a test function of a representation. -/
theorem groupDirectionalValue_test (φ : G →* Matrix N N 𝕜)
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b))
    (P Q : Matrix N N 𝕜) (ℓ : 𝕜 →L[ℝ] ℝ) (i j : N) (X : GroupLieAlgebra I G) :
    groupDirectionalValue I X (fun g => (ℓ ((P * φ g * Q) i j) : ℂ)) =
      fun g => (ℓ ((P * φ g * (matrixDifferential I φ X * Q)) i j) : ℂ) := by
  funext g
  unfold groupDirectionalValue
  have hfun : (fun h => (ℓ ((P * φ (g * h) * Q) i j) : ℂ)) =
      fun h => (ℓ (((P * φ g) * φ h * Q) i j) : ℂ) := by
    funext h
    simp only [map_mul, Matrix.mul_assoc]
  rw [hfun, mvfderiv_test hφ]
  simp only [Matrix.mul_assoc]
  rfl

/-- **The matrix differential is a Lie algebra homomorphism.** -/
theorem matrixDifferential_lie [CompleteSpace E] [I.Boundaryless]
    (φ : G →* Matrix N N 𝕜)
    (hφ : ∀ a b, ContMDiff I 𝓘(ℝ, 𝕜) ∞ (fun g => φ g a b)) (X Y : GroupLieAlgebra I G) :
    matrixDifferential I φ ⁅X, Y⁆ =
      matrixDifferential I φ X * matrixDifferential I φ Y -
        matrixDifferential I φ Y * matrixDifferential I φ X := by
  ext i j
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  have hcomm := groupDirectionalValue_commutator_of_vectorFieldCommutator I
    (smoothVectorFieldCommutator_proof (I := I) (M := G)) X Y
    (contMDiff_test hφ 1 1 ℓ i j) 1
  rw [groupDirectionalValue_test φ hφ, groupDirectionalValue_test φ hφ,
    groupDirectionalValue_test φ hφ, groupDirectionalValue_test φ hφ,
    groupDirectionalValue_test φ hφ] at hcomm
  simp only [map_one, Matrix.one_mul, Matrix.mul_one] at hcomm
  rw [Matrix.sub_apply, map_sub]
  exact_mod_cast hcomm

end Langlands.Geometry.Manifold.MatrixCoefficientLie
