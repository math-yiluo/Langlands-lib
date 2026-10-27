import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
import Langlands.Algebra.IdealTensorKernelSeparationStatement

/-! # Proof of mixed-scalar separation of ideal tensor kernels -/

universe u v w

open TensorProduct

namespace Langlands.Algebra

namespace IdealTensorKernelSeparationProof

variable {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- If `M` is finite over `S` and `N` is finite over `R`, then `M ⊗[R] N` is finite
over `S`. -/
theorem finite_tensor (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Finite S M] [Module.Finite R N] : Module.Finite S (M ⊗[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  have : Module.Finite S (M ⊗[R] (Fin n → R)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight R S M (Fin n)).symm
  exact Module.Finite.of_surjective (TensorProduct.AlgebraTensorModule.lTensor S M f)
    (LinearMap.lTensor_surjective M hf)

/-- The `R`-submodule `I ^ n • ⊤` lies in the `S`-submodule `(I S) ^ n • ⊤`. -/
theorem pow_smul_top_le (I : Ideal R) (n : ℕ) (P : Type*) [AddCommGroup P] [Module R P]
    [Module S P] [IsScalarTower R S P] :
    (I ^ n • ⊤ : Submodule R P) ≤
      ((I.map (algebraMap R S) ^ n • ⊤ : Submodule S P).restrictScalars R) := by
  rw [Submodule.smul_le]
  intro r hr y _
  rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r y]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hr

end IdealTensorKernelSeparationProof

open IdealTensorKernelSeparationProof in
/-- Mixed-scalar separation of ideal tensor kernels. -/
theorem idealTensorKernelSeparation : IdealTensorKernelSeparationStatement.{u, v, w} := by
  intro R S M _ _ _ _ _ _ _ _ _ _ I hJ hker
  rw [Module.Flat.iff_lTensor_injective']
  intro a
  have : Module.Finite S (M ⊗[R] a) := finite_tensor (S := S) a
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ (⨅ n : ℕ, I.map (algebraMap R S) ^ n • ⊤ : Submodule S (M ⊗[R] a)) :=
    (Submodule.mem_iInf _).mpr fun n => pow_smul_top_le (S := S) I n _ (hker a n hx)
  rw [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hJ] at hmem
  exact (Submodule.mem_bot S).mp hmem

end Langlands.Algebra
