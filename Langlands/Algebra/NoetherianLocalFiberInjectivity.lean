import Langlands.Algebra.NoetherianLocalFiberInjectivityStatement
import Langlands.Algebra.ResidueTensorNilpotentInjectivity
import Langlands.Algebra.NoetherianAdicTensorInjectivity
import Langlands.Algebra.IdealTensorCokernelFlatness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

universe u v w z

open TensorProduct

namespace Langlands.Algebra

/-- Noetherian lifting of residue-fibre injectivity, Stacks Project 00ME. -/
theorem noetherianLocalFiberInjectivity :
    NoetherianLocalFiberInjectivityStatement.{u,v,w,z} := by
  intro R S A B instR instS instLocalR instLocalS instNoeth instAlg instLocalHom
    instA instB instRA instSA instTower instFinite instRB f hB hres
  have hall (I : Ideal R) : Function.Injective (LinearMap.lTensor (R ⧸ I) f) := by
    apply noetherianAdicTensorInjectivity R S A B f I
    intro n
    apply residueTensorNilpotentInjectivity R A B
      (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ n)) f n hB hres
    intro r hr c
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
    change (Submodule.Quotient.mk (r • s) :
      R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ n)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact (I ⊔ IsLocalRing.maximalIdeal R ^ n).mul_mem_right s
      ((show IsLocalRing.maximalIdeal R ^ n ≤
        I ⊔ IsLocalRing.maximalIdeal R ^ n from le_sup_right) hr)
  have hf : Function.Injective f := by
    intro x y hxy
    have ht : (1 : R ⧸ (⊥ : Ideal R)) ⊗ₜ[R] x =
        (1 : R ⧸ (⊥ : Ideal R)) ⊗ₜ[R] y := by
      apply hall ⊥
      simp only [LinearMap.lTensor_tmul, hxy]
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul A (⊥ : Ideal R)) ht
    have hm : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R A)) := by
      apply (Submodule.Quotient.eq _).1
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using hq
    exact sub_eq_zero.mp (by simpa using hm)
  exact ⟨hf, idealTensorCokernelFlatness R A B f hB hf hall⟩

end Langlands.Algebra
