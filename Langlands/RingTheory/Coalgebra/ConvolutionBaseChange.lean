import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Scalar extension of finite convolution duals

The coalgebra and convolution structures in this module are Mathlib instances.
-/

open TensorProduct WithConv
open scoped Coalgebra

universe u v w

namespace Langlands.CoalgebraDescent

variable (k : Type u) [Field k]
variable (D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
variable (K : Type w) [Field K] [Algebra k K]

/-- Convolution on scalar-extended coalgebras, expanded along a finite
representation of the original comultiplication. -/
private theorem convMul_tmul
    (f g : WithConv ((K ⊗[k] D) →ₗ[K] K)) (b : K) (d : D) :
    (f * g) (b ⊗ₜ[k] d) =
      ∑ i ∈ (ℛ k d).index,
        f (1 ⊗ₜ[k] (ℛ k d).left i) * g (b ⊗ₜ[k] (ℛ k d).right i) := by
  rw [LinearMap.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply,
    ← (ℛ k d).eq]
  simp [TensorProduct.tmul_sum, map_sum]

variable [FiniteDimensional k D]

/-- The finite-dimensional dual base-change equivalence, with the convolution
synonyms restored on both duals. -/
noncomputable def convolutionDualBaseChangeLinearEquiv :
    K ⊗[k] WithConv (D →ₗ[k] k) ≃ₗ[K] WithConv ((K ⊗[k] D) →ₗ[K] K) :=
  ((WithConv.linearEquiv k (D →ₗ[k] k)).baseChange k K _ _).trans
    ((TensorProduct.isBaseChange k D K).toDualBaseChange.trans
      (WithConv.linearEquiv K ((K ⊗[k] D) →ₗ[K] K)).symm)

omit [Coalgebra k D] in
@[simp]
theorem convolutionDualBaseChangeLinearEquiv_tmul_apply
    (a b : K) (f : WithConv (D →ₗ[k] k)) (d : D) :
    convolutionDualBaseChangeLinearEquiv k D K (a ⊗ₜ[k] f) (b ⊗ₜ[k] d) =
      a * b * algebraMap k K (f d) := by
  change (TensorProduct.isBaseChange k D K).toDualBaseChange
    (a ⊗ₜ[k] f.ofConv) (b ⊗ₜ[k] d) = _
  rw [show b ⊗ₜ[k] d = b • (1 ⊗ₜ[k] d) by simp [smul_tmul']]
  have h : (TensorProduct.isBaseChange k D K).toDualBaseChange
      (a ⊗ₜ[k] f.ofConv) (1 ⊗ₜ[k] d) = a * algebraMap k K (f d) :=
    (TensorProduct.isBaseChange k D K).toDualBaseChange_tmul a f.ofConv d
  rw [map_smul, h]
  simp [mul_left_comm, mul_assoc]

/-- Scalar extension commutes with the convolution dual of a finite-dimensional
coalgebra. No cocommutativity or nonzero-dimension hypothesis is needed. -/
noncomputable def convolutionDualBaseChangeEquiv :
    K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] WithConv ((K ⊗[k] D) →ₗ[K] K) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (convolutionDualBaseChangeLinearEquiv k D K)
    (by
      intro a b f g
      apply WithConv.ext
      ext d
      change convolutionDualBaseChangeLinearEquiv k D K
          ((a * b) ⊗ₜ[k] (f * g)) (1 ⊗ₜ[k] d) =
        (convolutionDualBaseChangeLinearEquiv k D K (a ⊗ₜ[k] f) *
          convolutionDualBaseChangeLinearEquiv k D K (b ⊗ₜ[k] g)) (1 ⊗ₜ[k] d)
      rw [convMul_tmul k D K]
      simp [(ℛ k d).convMul_apply, map_sum,
        Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm])
    (by
      apply WithConv.ext
      ext d
      simp [LinearMap.convOne_apply, Algebra.smul_def])

/-- The algebra equivalence has exactly the finite dual base-change linear
equivalence as its underlying linear equivalence. -/
@[simp]
theorem convolutionDualBaseChangeEquiv_toLinearEquiv :
    (convolutionDualBaseChangeEquiv k D K).toLinearEquiv =
      convolutionDualBaseChangeLinearEquiv k D K := rfl

/-- The inverse algebra equivalence uses the inverse of the same linear
equivalence. -/
@[simp]
theorem convolutionDualBaseChangeEquiv_symm_toLinearEquiv :
    (convolutionDualBaseChangeEquiv k D K).symm.toLinearEquiv =
      (convolutionDualBaseChangeLinearEquiv k D K).symm := rfl

@[simp]
theorem convolutionDualBaseChangeEquiv_apply
    (x : K ⊗[k] WithConv (D →ₗ[k] k)) :
    convolutionDualBaseChangeEquiv k D K x =
      convolutionDualBaseChangeLinearEquiv k D K x := rfl

@[simp]
theorem convolutionDualBaseChangeEquiv_symm_apply
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)) :
    (convolutionDualBaseChangeEquiv k D K).symm f =
      (convolutionDualBaseChangeLinearEquiv k D K).symm f := rfl

/-- The canonical evaluation formula on pure tensors. -/
theorem convolutionDualBaseChangeEquiv_tmul_apply
    (a b : K) (f : WithConv (D →ₗ[k] k)) (d : D) :
    convolutionDualBaseChangeEquiv k D K (a ⊗ₜ[k] f) (b ⊗ₜ[k] d) =
      a * b * algebraMap k K (f d) :=
  convolutionDualBaseChangeLinearEquiv_tmul_apply k D K a b f d

/-- Evaluation recovers the original functional after the backward map. -/
theorem convolutionDualBaseChangeEquiv_apply_symm_apply
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)) (b : K) (d : D) :
    convolutionDualBaseChangeEquiv k D K
        ((convolutionDualBaseChangeEquiv k D K).symm f) (b ⊗ₜ[k] d) =
      f (b ⊗ₜ[k] d) := by
  rw [AlgEquiv.apply_symm_apply]

/-- The backward map recovers every tensor in the source. -/
theorem convolutionDualBaseChangeEquiv_symm_apply_apply
    (x : K ⊗[k] WithConv (D →ₗ[k] k)) :
    (convolutionDualBaseChangeEquiv k D K).symm
        (convolutionDualBaseChangeEquiv k D K x) = x :=
  (convolutionDualBaseChangeEquiv k D K).symm_apply_apply x

/-- In any finite basis, the inverse is the usual dual-basis expansion. In
particular this formula also applies to an empty basis of a zero coalgebra. -/
theorem convolutionDualBaseChangeEquiv_symm_apply_eq_sum
    {ι : Type*} [Fintype ι] (basis : Module.Basis ι k D)
    (f : WithConv ((K ⊗[k] D) →ₗ[K] K)) :
    (convolutionDualBaseChangeEquiv k D K).symm f =
      ∑ i, f (1 ⊗ₜ[k] basis i) ⊗ₜ[k] toConv (basis.coord i) := by
  apply (convolutionDualBaseChangeEquiv k D K).injective
  rw [AlgEquiv.apply_symm_apply, map_sum]
  apply WithConv.ext
  ext d
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, ofConv_sum, LinearMap.sum_apply]
  change f (1 ⊗ₜ[k] d) =
    ∑ i, convolutionDualBaseChangeEquiv k D K
      (f (1 ⊗ₜ[k] basis i) ⊗ₜ[k] toConv (basis.coord i)) (1 ⊗ₜ[k] d)
  simp only [convolutionDualBaseChangeEquiv_tmul_apply, mul_one]
  conv_lhs => rw [← basis.sum_repr d, TensorProduct.tmul_sum, map_sum]
  simp only [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, Algebra.smul_def,
    Module.Basis.coord_apply, mul_comm]

end Langlands.CoalgebraDescent
