/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Trace

/-!
# The categorical trace of an endomorphism of a finite free module

Let `R` be a commutative ring and `M` an `R`-module with a finite basis `b`. Then `M` has the
right dual `Hom_R(M, R)` in `ModuleCat R` (`ModuleCat.exactPairingOfBasis`): the coevaluation is
`1 ↦ ∑ᵢ bᵢ ⊗ bᵢ*` and the evaluation is the contraction `φ ⊗ m ↦ φ(m)`.

For the symmetric braiding of `ModuleCat R`, the categorical trace
`CategoryTheory.MonoidalCategory.trace` of an endomorphism `f` of a finite free module `M` is the
usual trace `LinearMap.trace R M f`, as an element of `End (𝟙_ (ModuleCat R))`
(`ModuleCat.trace_eq_algebraMap_linearMapTrace`). This holds for any right dual of `M`.

This is used for blueprint `proposition-properties-trace` and `proposition-properties-trace--4`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R]

section

variable {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι R M)

/-- The first triangle identity for the coevaluation `1 ↦ ∑ᵢ bᵢ ⊗ bᵢ*` of a finite basis and the
contraction. -/
lemma contractLeft_lTensor_comp_assoc_comp_rTensor_toSpanSingleton :
    (contractLeft R M).lTensor M ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
      (LinearMap.toSpanSingleton R _ (∑ i, b i ⊗ₜ[R] b.coord i)).rTensor M =
      (TensorProduct.rid R M).symm.toLinearMap ∘ₗ (TensorProduct.lid R M).toLinearMap := by
  refine TensorProduct.ext' fun r q ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.lid_tmul,
    TensorProduct.rid_symm_apply, ← smul_tmul', map_smul, sum_tmul, map_sum,
    TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, contractLeft_apply]
  congr 1
  conv_rhs => rw [← b.sum_repr q, sum_tmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_tmul, smul_eq_mul, mul_one, Module.Basis.coord_apply]

/-- The second triangle identity for the coevaluation `1 ↦ ∑ᵢ bᵢ ⊗ bᵢ*` of a finite basis and the
contraction. -/
lemma contractLeft_rTensor_comp_assoc_symm_comp_lTensor_toSpanSingleton :
    (contractLeft R M).rTensor (Module.Dual R M) ∘ₗ
      (TensorProduct.assoc R _ _ _).symm.toLinearMap ∘ₗ
        (LinearMap.toSpanSingleton R _ (∑ i, b i ⊗ₜ[R] b.coord i)).lTensor (Module.Dual R M) =
      (TensorProduct.lid R _).symm.toLinearMap ∘ₗ (TensorProduct.rid R _).toLinearMap := by
  refine TensorProduct.ext' fun φ r ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.rid_tmul,
    TensorProduct.lid_symm_apply, tmul_smul, map_smul, tmul_sum, map_sum,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, contractLeft_apply]
  congr 1
  conv_rhs => rw [← b.sum_dual_apply_smul_coord φ, tmul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← smul_tmul, smul_eq_mul, mul_one]

end

/-- A module `M` with a finite basis `b` is paired with its dual `Hom_R(M, R)` in `ModuleCat R`:
the coevaluation is `1 ↦ ∑ᵢ bᵢ ⊗ bᵢ*` and the evaluation is the contraction. -/
@[instance_reducible]
noncomputable def exactPairingOfBasis (M : ModuleCat.{u} R) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R M) : ExactPairing M (of R (Module.Dual R M)) where
  coevaluation' := ofHom (LinearMap.toSpanSingleton R _ (∑ i, b i ⊗ₜ[R] b.coord i))
  evaluation' := ofHom (contractLeft R M)
  coevaluation_evaluation' := by
    ext : 1
    exact contractLeft_rTensor_comp_assoc_symm_comp_lTensor_toSpanSingleton b
  evaluation_coevaluation' := by
    ext : 1
    exact contractLeft_lTensor_comp_assoc_comp_rTensor_toSpanSingleton b

/-- A finite free module `M` has the right dual `Hom_R(M, R)` in `ModuleCat R`. -/
@[instance_reducible]
noncomputable def hasRightDualOfFree (M : ModuleCat.{u} R) [Module.Free R M]
    [Module.Finite R M] : HasRightDual M :=
  letI := exactPairingOfBasis M (Module.Free.chooseBasis R M)
  ⟨of R (Module.Dual R M)⟩

/-- The categorical trace of an endomorphism `f` of a finite free module `M`, for the symmetric
braiding of `ModuleCat R` and any right dual of `M`, is the trace `LinearMap.trace R M f`. -/
theorem trace_eq_algebraMap_linearMapTrace {M : ModuleCat.{u} R} [HasRightDual M]
    [Module.Free R M] [Module.Finite R M] (f : M ⟶ M) :
    trace f = (algebraMap R (End (𝟙_ (ModuleCat.{u} R))) (LinearMap.trace R M f.hom)).asHom := by
  classical
  let b := Module.Free.chooseBasis R M
  let := exactPairingOfBasis M b
  rw [trace_eq_of_exactPairing (Y := of R (Module.Dual R M)),
    Algebra.algebraMap_eq_smul_one, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  have h₁ : η_ M (of R (Module.Dual R M)) =
      ofHom (LinearMap.toSpanSingleton R _ (∑ i, b i ⊗ₜ[R] b.coord i)) := rfl
  have h₂ : ε_ M (of R (Module.Dual R M)) = ofHom (contractLeft R M) := rfl
  rw [h₁, h₂]
  ext : 1
  refine LinearMap.ext_ring ?_
  simp only [hom_comp, LinearMap.comp_apply, hom_ofHom]
  erw [LinearMap.toSpanSingleton_apply, one_smul]
  simp only [map_sum, LinearMap.toMatrix_apply, Matrix.diag_apply]
  exact (Finset.sum_congr rfl fun i _ ↦ rfl).trans (mul_one _).symm

end ModuleCat
