import Langlands.Algebra.NoetherianAdicTensorInjectivityStatement
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic

universe u v w z

open TensorProduct LinearMap

namespace Langlands.Algebra

/-- Injectivity after every maximal-ideal thickening implies injectivity
after quotienting by the original ideal. -/
theorem noetherianAdicTensorInjectivity :
    NoetherianAdicTensorInjectivityStatement.{u,v,w,z} := by
  intro R S A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ f I h
  let m := IsLocalRing.maximalIdeal R
  let J : Ideal S := m.map (algebraMap R S)
  let P : Submodule S A := I.map (algebraMap R S) • ⊤
  have hP : P.restrictScalars R = I • (⊤ : Submodule R A) := by
    simpa only [P, Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule S A)
  let Q := A ⧸ P
  let q : A →ₗ[R] Q := P.mkQ.restrictScalars R
  have hJ : J ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hKrull : (⨅ n : ℕ, J ^ n • ⊤ : Submodule S Q) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J hJ
  have hquot (n : ℕ) :
      (I ⊔ m ^ n) • (⊤ : Submodule R A) ≤
        ((J ^ n • (⊤ : Submodule S Q)).restrictScalars R).comap q := by
    apply Submodule.smul_le.mpr
    intro r hr a _
    obtain ⟨i, hi, t, ht, rfl⟩ := Submodule.mem_sup.mp hr
    change q ((i + t) • a) ∈ J ^ n • (⊤ : Submodule S Q)
    rw [add_smul, map_add]
    have hi0 : q (i • a) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      change i • a ∈ P.restrictScalars R
      rw [hP]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    rw [hi0, zero_add, map_smul]
    rw [← IsScalarTower.algebraMap_smul S t (q a)]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    change algebraMap R S t ∈ m.map (algebraMap R S) ^ n
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ht
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  let e := TensorProduct.quotTensorEquivQuotSMul A I
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R A)) (e x)
  have hxrep : (1 : R ⧸ I) ⊗ₜ[R] a = x := by
    apply e.injective
    simpa only [e, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
      Submodule.mkQ_apply] using ha
  have hfa : f a ∈ I • (⊤ : Submodule R B) := by
    have ht : (1 : R ⧸ I) ⊗ₜ[R] f a = 0 := by
      simpa only [← hxrep, LinearMap.lTensor_tmul] using hx
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul B I) ht
    apply (Submodule.Quotient.mk_eq_zero _).mp
    simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using hq
  have haN (n : ℕ) : a ∈ (I ⊔ m ^ n) • (⊤ : Submodule R A) := by
    have hfaN : f a ∈ (I ⊔ m ^ n) • (⊤ : Submodule R B) :=
      (Submodule.smul_mono_left le_sup_left) hfa
    have ht : (1 : R ⧸ (I ⊔ m ^ n)) ⊗ₜ[R] f a = 0 := by
      apply (TensorProduct.quotTensorEquivQuotSMul B (I ⊔ m ^ n)).injective
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using
        (Submodule.Quotient.mk_eq_zero _).mpr hfaN
    have hat : (1 : R ⧸ (I ⊔ m ^ n)) ⊗ₜ[R] a = 0 :=
      h n (by simpa only [LinearMap.lTensor_tmul, map_zero] using ht)
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul A (I ⊔ m ^ n)) hat
    apply (Submodule.Quotient.mk_eq_zero _).mp
    simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using hq
  have hqa : q a = 0 := by
    have hm : q a ∈ (⨅ n : ℕ, J ^ n • ⊤ : Submodule S Q) :=
      (Submodule.mem_iInf _).mpr fun n => hquot n (haN n)
    rw [hKrull] at hm
    exact (Submodule.mem_bot S).mp hm
  have haI : a ∈ I • (⊤ : Submodule R A) := by
    rw [← hP]
    exact (Submodule.Quotient.mk_eq_zero P).mp hqa
  rw [← hxrep]
  apply e.injective
  simpa only [e, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using
    (Submodule.Quotient.mk_eq_zero _).mpr haI

end Langlands.Algebra
