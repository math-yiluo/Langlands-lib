import Langlands.Algebra.AlgebraTensorSimpleModuleStatements
import Langlands.Algebra.RankOneGradedAlgebra
import Mathlib.LinearAlgebra.Contraction

open scoped TensorProduct
noncomputable section
namespace Langlands.AlgebraTensor

universe u₁ u₂ v v₁ v₂ w₁ w₂

variable {A₁ : Type u₁} {A₂ : Type u₂} [Ring A₁] [Algebra ℂ A₁]
  [Ring A₂] [Algebra ℂ A₂]
variable {V₁ : Type v₁} {V₂ : Type v₂}
  [AddCommGroup V₁] [Module ℂ V₁] [Module A₁ V₁] [IsScalarTower ℂ A₁ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [Module A₂ V₂] [IsScalarTower ℂ A₂ V₂]

abbrev action : A₁ ⊗[ℂ] A₂ →ₐ[ℂ] Module.End ℂ (V₁ ⊗[ℂ] V₂) :=
  (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V₁) (Algebra.lsmul ℂ ℂ V₂))

@[simp] theorem action_tmul (a : A₁) (b : A₂) (x : V₁) (y : V₂) :
    action (a ⊗ₜ b) (x ⊗ₜ y) = (a • x) ⊗ₜ (b • y) := by
  simp [action, Module.endTensorEndAlgHom_apply]

theorem action_surjective [FiniteDimensional ℂ V₁] [IsSimpleModule A₁ V₁]
    [FiniteDimensional ℂ V₂] [IsSimpleModule A₂ V₂] :
    Function.Surjective (action (A₁ := A₁) (A₂ := A₂) (V₁ := V₁) (V₂ := V₂)) := by
  intro f
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V₁ V₂ V₁ V₂).surjective f
  induction t with
  | tmul g h =>
    obtain ⟨a, ha⟩ := RankOneGraded.exists_forall_eq_smul_of_isSimpleModule (A := A₁) g
    obtain ⟨b, hb⟩ := RankOneGraded.exists_forall_eq_smul_of_isSimpleModule (A := A₂) h
    refine ⟨a ⊗ₜ b, TensorProduct.ext' fun x y => ?_⟩
    rw [action_tmul]
    simp [homTensorHomEquiv_apply, ha, hb]
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

theorem stable_eq_bot_or_top [FiniteDimensional ℂ V₁] [IsSimpleModule A₁ V₁]
    [FiniteDimensional ℂ V₂] [IsSimpleModule A₂ V₂]
    (U : Submodule ℂ (V₁ ⊗[ℂ] V₂))
    (hU : ∀ a x, x ∈ U → action (A₁ := A₁) (A₂ := A₂) a x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨a, ha⟩ := action_surjective (A₁ := A₁) (A₂ := A₂) (φ.smulRight y)
  have hmem := hU a x hx
  rwa [ha, LinearMap.smulRight_apply, hφ, one_smul] at hmem

end Langlands.AlgebraTensor

namespace Langlands
universe u₁ u₂ v₁ v₂

theorem algebraExternalTensorSimple : AlgebraExternalTensorSimpleStatement.{u₁, u₂, v₁, v₂} := by
  intro A₁ A₂ _ _ _ _ V₁ V₂ _ _ _ _ _ _ _ _ h₁ s₁ h₂ s₂
  have := h₁
  have := s₁
  have := h₂
  have := s₂
  have := IsSimpleModule.nontrivial A₁ V₁
  have := IsSimpleModule.nontrivial A₂ V₂
  exact ⟨inferInstance, AlgebraTensor.stable_eq_bot_or_top⟩

end Langlands
