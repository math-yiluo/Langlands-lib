import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite projective scalar extension of continuous functions -/

noncomputable section

open TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (A B X : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]
  [TopologicalSpace X]

/-- Extend a continuous scalar-valued function and multiply it by a tensor coefficient. -/
def continuousMapTensorAlgHom : B ⊗[A] C(X, A) →ₐ[B] C(X, B) :=
  AlgHom.liftEquiv A B C(X, A) C(X, B)
    (AlgHom.compLeftContinuous A (Algebra.ofId A B)
      (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A B)))

@[simp]
theorem continuousMapTensorAlgHom_tmul (b : B) (f : C(X, A)) (x : X) :
    continuousMapTensorAlgHom A B X (b ⊗ₜ[A] f) x =
      b * algebraMap A B (f x) := by
  rfl

theorem continuousMapTensorAlgHom_bijective [Module.Finite A B] [Module.Projective A B] :
    Function.Bijective (continuousMapTensorAlgHom A B X) := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  let b : Fin n → B := fun j ↦ p (Pi.single j 1)
  let φ : Fin n → B →ₗ[A] A := fun j ↦ LinearMap.proj j ∘ₗ s
  have hsum (y : B) : ∑ j, φ j y • b j = y := by
    simpa only [φ, b, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.id_apply,
      ← map_smul, ← map_sum, ← pi_eq_sum_univ'] using LinearMap.congr_fun hps y
  let coord : Fin n → B ⊗[A] C(X, A) →ₗ[A] C(X, A) :=
    fun j ↦ TensorProduct.lift (LinearMap.lsmul A C(X, A) ∘ₗ φ j)
  have hcoord (j : Fin n) (y : B) (f : C(X, A)) :
      coord j (y ⊗ₜ[A] f) = φ j y • f := rfl
  have hreconstruct (z : B ⊗[A] C(X, A)) :
      ∑ j, b j ⊗ₜ[A] coord j z = z := by
    induction z with
    | tmul y f => simp [hcoord, smul_tmul', ← sum_tmul, hsum]
    | add z w hz hw => simp [tmul_add, Finset.sum_add_distrib, hz, hw]
  have hcoord_eval (j : Fin n) (z : B ⊗[A] C(X, A)) (x : X) :
      coord j z x = φ j (continuousMapTensorAlgHom A B X z x) := by
    induction z with
    | tmul y f =>
      change φ j y * f x = φ j (y * algebraMap A B (f x))
      rw [mul_comm y, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | add z w hz hw => simp [hz, hw]
  refine ⟨?_, ?_⟩
  · intro z w hzw
    rw [← hreconstruct z, ← hreconstruct w]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ext x
    rw [hcoord_eval, hcoord_eval, hzw]
  · intro f
    let c : Fin n → C(X, A) := fun j ↦
      ⟨fun x ↦ φ j (f x),
        (IsModuleTopology.continuous_of_linearMap (φ j)).comp f.continuous⟩
    refine ⟨∑ j, b j ⊗ₜ[A] c j, ?_⟩
    ext x
    simpa [c, mul_comm, ← Algebra.smul_def] using hsum (f x)

/-- Continuous functions commute with finite projective extension of scalars. -/
def continuousMapTensorAlgEquiv [Module.Finite A B] [Module.Projective A B] :
    B ⊗[A] C(X, A) ≃ₐ[B] C(X, B) :=
  AlgEquiv.ofBijective (continuousMapTensorAlgHom A B X)
    (continuousMapTensorAlgHom_bijective A B X)

@[simp]
theorem continuousMapTensorAlgEquiv_apply [Module.Finite A B] [Module.Projective A B]
    (z : B ⊗[A] C(X, A)) :
    continuousMapTensorAlgEquiv A B X z = continuousMapTensorAlgHom A B X z := rfl

/-- Evaluation after the comparison is scalar extension of evaluation followed
by the canonical tensor-unit isomorphism. -/
theorem eval_comp_continuousMapTensorAlgEquiv [Module.Finite A B] [Module.Projective A B]
    (x : X) :
    (ContinuousMap.evalAlgHom B B x).comp (continuousMapTensorAlgEquiv A B X).toAlgHom =
      (Algebra.TensorProduct.rid A B B).toAlgHom.comp
        (Algebra.TensorProduct.lTensor B (ContinuousMap.evalAlgHom A A x)) := by
  apply AlgHom.ext
  intro z
  induction z with
  | tmul b f => simp [Algebra.smul_def, mul_comm]
  | add z w hz hw => simpa using congrArg₂ (· + ·) hz hw

end Langlands.AlgebraicGeometry.PointTopology
