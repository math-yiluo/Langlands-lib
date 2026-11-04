import Langlands.GroupScheme.Lie.ElementCentralizerTangent
import Mathlib.Algebra.Algebra.Bilinear

/-! # Matrix kernels of actual Lie-element centralizers -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}}
    {A : Type u} [CommRing A] [Algebra R A]
    {n : Type} [Fintype n] [DecidableEq n]

/-- A first-order matrix point fixes a constant tangent vector precisely when
its two original coefficient matrices commute. -/
theorem generalLinear_conjugation_constant_eq_iff (M N : Matrix n n A) :
    lieKernelConjugation (GeneralLinear.groupScheme n R) (pointUnit M)
      (pointKernelEquiv (N.map (TrivSqZeroExt.inlHom A A))) =
        pointKernelEquiv (N.map (TrivSqZeroExt.inlHom A A)) ↔ Commute M N := by
  have hcalc :
      lieKernelConjugation (GeneralLinear.groupScheme n R) (pointUnit M)
        (pointKernelEquiv (N.map (TrivSqZeroExt.inlHom A A))) =
      pointKernelEquiv
        (N.map (TrivSqZeroExt.inlHom A A) + epsilonMatrix (M * N - N * M)) := by
    apply Subtype.ext
    change constant _ (pointUnit M) * pointUnit _ * (constant _ (pointUnit M))⁻¹ = _
    rw [pointUnit_conjugation, pointUnit_matrix, matrixUnit_conjugate_constant]
    rfl
  rw [hcalc]
  constructor
  · intro h
    have hm := (pointKernelEquiv (n := n) (R := R) (S := DualNumber A)).injective h
    have he := add_eq_left.mp hm
    apply (commute_iff_eq _ _).2
    apply sub_eq_zero.mp
    apply Matrix.ext
    intro i j
    exact congrArg TrivSqZeroExt.snd (congrArg (fun B : Matrix n n (DualNumber A) => B i j) he)
  · intro h
    rw [h.eq, sub_self, epsilonMatrix_zero, add_zero]

variable {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- An injective actual representation identifies the tangent carrier of the
all-test element centralizer with the ordinary commuting-matrix condition. -/
theorem mem_elementCentralizerLie_iff_commute_tangentMatrix
    (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom)
    (X Y : lieKernel G R) :
    Additive.ofMul Y ∈ elementCentralizerLie G X ↔
      Commute (ρ.tangentMatrix R Y) (ρ.tangentMatrix R X) := by
  change Y.val ∈ (elementCentralizer G X).carrier _ ↔ _
  rw [mem_elementCentralizer_affine_iff]
  rw [← (lieKernelTarget_injective ρ (DualNumber R) hρ).eq_iff,
    targetMap_conjugation]
  have hY : Y.val ≫ ρ.hom.hom = pointUnit (ρ.tangentMatrix R Y) :=
    (congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix R Y)).symm
  have hX : targetMap ρ (DualNumber R)
      (lieKernelMap G (Algebra.ofId R (DualNumber R)) X) =
      pointKernelEquiv ((ρ.tangentMatrix R X).map (TrivSqZeroExt.inlHom R R)) := by
    rw [← ρ.pointKernelEquiv_tangentMatrix, ρ.tangentMatrix_naturality]
    rfl
  rw [hY, hX, generalLinear_conjugation_constant_eq_iff]

/-- The matrix commutator with a fixed actual tangent vector, as a linear map
on the actual Lie module. -/
def tangentCommutator (ρ : MatrixRepresentation G n) (X : lieKernel G R) :
    Additive (lieKernel G R) →ₗ[R] Matrix n n R :=
  (LinearMap.mulRight R (ρ.tangentMatrix R X) -
    LinearMap.mulLeft R (ρ.tangentMatrix R X)).comp (ρ.kernelDifferential R)

@[simp]
theorem tangentCommutator_apply (ρ : MatrixRepresentation G n)
    (X Y : lieKernel G R) :
    tangentCommutator ρ X (Additive.ofMul Y) =
      ρ.tangentMatrix R Y * ρ.tangentMatrix R X -
        ρ.tangentMatrix R X * ρ.tangentMatrix R Y := rfl

/-- The tangent submodule of the all-test centralizer is exactly a matrix
commutator kernel for every monomorphic actual matrix representation. -/
theorem elementCentralizerLie_eq_ker_tangentCommutator
    (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom) (X : lieKernel G R) :
    elementCentralizerLie G X = LinearMap.ker (tangentCommutator ρ X) := by
  ext Y
  change Additive.ofMul Y.toMul ∈ elementCentralizerLie G X ↔
    Additive.ofMul Y.toMul ∈ LinearMap.ker (tangentCommutator ρ X)
  rw [mem_elementCentralizerLie_iff_commute_tangentMatrix ρ hρ,
    LinearMap.mem_ker, tangentCommutator_apply, sub_eq_zero]
  exact commute_iff_eq _ _

/-- A tangent centralizer is the whole Lie module exactly when its fixed
matrix commutes with every actual tangent matrix. -/
theorem elementCentralizerLie_eq_top_iff_commute_tangentMatrix
    (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom) (X : lieKernel G R) :
    elementCentralizerLie G X = ⊤ ↔
      ∀ Y : lieKernel G R, Commute (ρ.tangentMatrix R Y) (ρ.tangentMatrix R X) := by
  rw [Submodule.eq_top_iff']
  constructor
  · intro h Y
    exact (mem_elementCentralizerLie_iff_commute_tangentMatrix ρ hρ X Y).mp
      (h (Additive.ofMul Y))
  · intro h Y
    exact (mem_elementCentralizerLie_iff_commute_tangentMatrix ρ hρ X Y.toMul).mpr
      (h Y.toMul)

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Actual tangent centralizer membership is symmetric for affine algebraic
groups, as follows from one closed matrix embedding. -/
theorem mem_elementCentralizerLie_comm (X Y : lieKernel G k) :
    Additive.ofMul Y ∈ elementCentralizerLie G X ↔
      Additive.ofMul X ∈ elementCentralizerLie G Y := by
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hm : Mono ρ.hom.hom := Over.mono_of_mono_left _
  rw [mem_elementCentralizerLie_iff_commute_tangentMatrix ρ hm,
    mem_elementCentralizerLie_iff_commute_tangentMatrix ρ hm]
  exact ⟨Commute.symm, Commute.symm⟩

end Langlands.GroupScheme.Lie
