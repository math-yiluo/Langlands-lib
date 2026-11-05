import Langlands.GroupScheme.Lie.ElementCentralizerTangent
import Langlands.GroupScheme.Lie.ScalarExtension

/-! # The tangent image of a representation is closed under commutators -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open GeneralLinear.DualNumber

namespace Lie

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- A dual-number point `1 + εM` conjugates the constant lift of `N` to
`N + ε(MN - NM)`. -/
theorem generalLinear_conjugation_constant {n : Type} [Fintype n] [DecidableEq n]
    (M N : Matrix n n A) :
    lieKernelConjugation (GeneralLinear.groupScheme n R) (pointUnit M)
      (pointKernelEquiv (N.map (TrivSqZeroExt.inlHom A A))) =
        pointKernelEquiv (N.map (TrivSqZeroExt.inlHom A A) + epsilonMatrix (M * N - N * M)) := by
  apply Subtype.ext
  change constant _ (pointUnit M) * pointUnit _ * (constant _ (pointUnit M))⁻¹ = _
  rw [pointUnit_conjugation, pointUnit_matrix, matrixUnit_conjugate_constant]
  rfl

end Lie

namespace MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Entrywise epsilon coefficients of a dual-number matrix. -/
def epsilonCoefficients : Matrix n n (DualNumber k) →ₗ[k] Matrix n n k where
  toFun M := M.map TrivSqZeroExt.snd
  map_add' M N := by ext; rfl
  map_smul' c M := by ext; rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem epsilonCoefficients_apply (M : Matrix n n (DualNumber k)) (i j : n) :
    epsilonCoefficients M i j = (M i j).snd := rfl

/-- The epsilon part of a dual-number Lie-kernel point: under the scalar
extension `D ⊗[k] 𝔤 ≃ 𝔤_D`, the tensor `a ⊗ x` goes to `(snd a) • x`. -/
def epsilonPart (z : Additive (lieKernel G (DualNumber k))) : Additive (lieKernel G k) :=
  TensorProduct.lift ((LinearMap.lsmul k (Additive (lieKernel G k))).comp
      (TrivSqZeroExt.sndHom k k))
    ((Lie.kernelScalarExtension G (DualNumber k)).symm z)

/-- The epsilon coefficients of a tangent matrix over the dual numbers are the
tangent matrix of the epsilon part, uniformly in the representation. -/
theorem epsilonCoefficients_kernelDifferential (ρ : MatrixRepresentation G n)
    (z : Additive (lieKernel G (DualNumber k))) :
    epsilonCoefficients (ρ.kernelDifferential (DualNumber k) z) =
      ρ.kernelDifferential k (epsilonPart z) := by
  obtain ⟨t, rfl⟩ := (Lie.kernelScalarExtension G (DualNumber k)).surjective z
  rw [epsilonPart, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
    change epsilonCoefficients _ = ρ.kernelDifferential k (a.snd • x)
    symm
    rw [Lie.kernelScalarExtension_tmul, map_smul, map_smul, kernelDifferential_apply,
      kernelDifferential_apply]
    change _ = epsilonCoefficients (a • ρ.tangentMatrix (DualNumber k)
      (lieKernelMap G (Algebra.ofId k (DualNumber k)) x.toMul))
    rw [tangentMatrix_naturality]
    ext i j
    simp only [Matrix.smul_apply, epsilonCoefficients_apply, Matrix.map_apply, smul_eq_mul]
    change _ = (a * algebraMap k (DualNumber k) _).snd
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, TrivSqZeroExt.snd_smul]
    rw [smul_eq_mul, mul_comm]
  | add s t hs ht =>
    simp only [map_add, hs, ht]

/-- A Lie-kernel element whose tangent matrix, in every finite matrix
representation, is the commutator of the tangent matrices of `X` and `Y`. -/
def kernelBracket (X Y : lieKernel G k) : lieKernel G k :=
  (epsilonPart (Additive.ofMul (lieKernelConjugation G X.val
    (lieKernelMap G (Algebra.ofId k (DualNumber k)) Y)))).toMul

/-- The tangent matrix of `kernelBracket X Y` is the commutator of the tangent
matrices of `X` and `Y`. -/
theorem tangentMatrix_kernelBracket (ρ : MatrixRepresentation G n) (X Y : lieKernel G k) :
    ρ.tangentMatrix k (kernelBracket X Y) =
      ρ.tangentMatrix k X * ρ.tangentMatrix k Y -
        ρ.tangentMatrix k Y * ρ.tangentMatrix k X := by
  set M := ρ.tangentMatrix k X
  set N := ρ.tangentMatrix k Y
  let Z : lieKernel G (DualNumber k) := lieKernelConjugation G X.val
    (lieKernelMap G (Algebra.ofId k (DualNumber k)) Y)
  have hX : X.val ≫ ρ.hom.hom = pointUnit M :=
    (congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix k X)).symm
  have hY : Lie.targetMap ρ (DualNumber k)
      (lieKernelMap G (Algebra.ofId k (DualNumber k)) Y) =
      pointKernelEquiv (N.map (TrivSqZeroExt.inlHom k k)) := by
    rw [← ρ.pointKernelEquiv_tangentMatrix, ρ.tangentMatrix_naturality]
    rfl
  have hZ : ρ.tangentMatrix (DualNumber k) Z =
      N.map (TrivSqZeroExt.inlHom k k) + epsilonMatrix (M * N - N * M) := by
    apply (pointKernelEquiv (R := CommRingCat.of k)).injective
    rw [ρ.pointKernelEquiv_tangentMatrix, Lie.targetMap_conjugation, hX, hY,
      Lie.generalLinear_conjugation_constant]
  have h := epsilonCoefficients_kernelDifferential ρ (Additive.ofMul Z)
  rw [kernelDifferential_apply, kernelDifferential_apply, toMul_ofMul, hZ] at h
  change ρ.tangentMatrix k (epsilonPart (Additive.ofMul Z)).toMul = _
  rw [← h]
  ext i j
  simp [epsilonMatrix_apply]

/-- The commutator of two tangent matrices is again a tangent matrix. -/
theorem tangentMatrix_commutator_mem (ρ : MatrixRepresentation G n) (X Y : lieKernel G k) :
    ρ.tangentMatrix k X * ρ.tangentMatrix k Y - ρ.tangentMatrix k Y * ρ.tangentMatrix k X ∈
      LinearMap.range (ρ.kernelDifferential k) :=
  ⟨Additive.ofMul (kernelBracket X Y), tangentMatrix_kernelBracket ρ X Y⟩

end MatrixRepresentation

end Langlands.GroupScheme
