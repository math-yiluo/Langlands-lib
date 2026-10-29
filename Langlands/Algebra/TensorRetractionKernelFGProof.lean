import Langlands.Algebra.TensorRetractionKernelFGStatement
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Proof of finite generation of the canonical tensor retraction kernel -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Proof of `TensorRetractionKernelFGStatement`: for the finite essential generators `σ`
of `S` over `R`, the kernel of `μ : S ⊗[R] T →ₐ[S] T` is spanned by the elements
`s ⊗ 1 - 1 ⊗ algebraMap S T s`, `s ∈ σ`. -/
theorem tensorRetractionKernelFG : TensorRetractionKernelFGStatement.{u, v, w} := by
  intro R S T _ _ _ _ _ _ _ hS
  classical
  let μ : S ⊗[R] T →ₐ[S] T := (AlgHom.liftEquiv R S T T) (AlgHom.id R T)
  let gens : Finset (S ⊗[R] T) := (Algebra.EssFiniteType.finset R S).image
    fun s ↦ s ⊗ₜ[R] (1 : T) - (1 : S) ⊗ₜ[R] algebraMap S T s
  refine ⟨gens, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image, Ideal.span_le]
    rintro _ ⟨s, _, rfl⟩
    simp [RingHom.mem_ker, Algebra.smul_def]
  · intro x hx
    let J : Ideal (S ⊗[R] T) := Ideal.span gens
    let q : S ⊗[R] T →ₐ[R] S ⊗[R] T ⧸ J := IsScalarTower.toAlgHom R (S ⊗[R] T) _
    have key : q.comp Algebra.TensorProduct.includeLeft =
        (q.comp Algebra.TensorProduct.includeRight).comp (IsScalarTower.toAlgHom R S T) := by
      apply Algebra.EssFiniteType.algHom_ext
      intro a ha
      simp only [q, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      refine Ideal.subset_span ?_
      simp only [gens, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨a, ha, rfl⟩
    have hall : ∀ y : S ⊗[R] T, q y = q ((1 : S) ⊗ₜ[R] μ y) := by
      intro y
      induction y with
      | tmul s t =>
        have hs : q (s ⊗ₜ[R] (1 : T)) = q ((1 : S) ⊗ₜ[R] algebraMap S T s) := by
          simpa using AlgHom.congr_fun key s
        calc q (s ⊗ₜ[R] t) = q (s ⊗ₜ[R] (1 : T)) * q ((1 : S) ⊗ₜ[R] t) := by
              rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = q ((1 : S) ⊗ₜ[R] algebraMap S T s) * q ((1 : S) ⊗ₜ[R] t) := by rw [hs]
          _ = q ((1 : S) ⊗ₜ[R] μ (s ⊗ₜ[R] t)) := by
              rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
              simp [μ, Algebra.smul_def]
      | add a b ha hb => rw [map_add, ha, hb, ← map_add, ← TensorProduct.tmul_add, ← map_add]
    have hx0 := hall x
    rw [show μ x = 0 from RingHom.mem_ker.mp hx, TensorProduct.tmul_zero, map_zero] at hx0
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx0

end Langlands.Algebra
