import Langlands.Representation.Shahidi.LocalCoefficientPadic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Binary tensor coordinates for the Shahidi pair carrier

Specializations and intrinsic identities for the published `pairSplit`, `pairFlip`
and `pairFunctional`. All constructions are algebraic.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shahidi

universe uV uF

variable (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]

/-- The published induction carrier in ordinary binary tensor coordinates. -/
abbrev pairTensorEquiv : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] V₁ ⊗[ℂ] V₂ :=
  pairSplit (pairCarrier V₁ V₂)

variable {V₁ V₂}

@[simp]
theorem pairTensorEquiv_pairTensor (v₁ : V₁) (v₂ : V₂) :
    pairTensorEquiv V₁ V₂ (pairTensor v₁ v₂) = v₁ ⊗ₜ[ℂ] v₂ :=
  pairSplit_tprod _ _

@[simp]
theorem pairTensorEquiv_symm_tmul (v₁ : V₁) (v₂ : V₂) :
    (pairTensorEquiv V₁ V₂).symm (v₁ ⊗ₜ[ℂ] v₂) = pairTensor v₁ v₂ := by
  apply (pairTensorEquiv V₁ V₂).injective
  simp

/-- The existing flip is exactly transport of binary tensor commutativity. -/
theorem pairFlip_eq_transport :
    (pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] _) =
      (pairTensorEquiv V₁ V₂).trans
        ((TensorProduct.comm ℂ V₁ V₂).trans (pairTensorEquiv V₂ V₁).symm) := by
  ext x
  change (pairTensorEquiv V₂ V₁).symm
    (TensorProduct.congr (LinearEquiv.refl ℂ V₂) (LinearEquiv.refl ℂ V₁)
      (TensorProduct.comm ℂ V₁ V₂ (pairTensorEquiv V₁ V₂ x))) =
    (pairTensorEquiv V₂ V₁).symm
      (TensorProduct.comm ℂ V₁ V₂ (pairTensorEquiv V₁ V₂ x))
  rw [TensorProduct.congr_refl_refl, LinearEquiv.refl_apply]

@[simp]
theorem pairTensorEquiv_pairFlip (x : PiTensorProduct ℂ (pairCarrier V₁ V₂)) :
    pairTensorEquiv V₂ V₁ (pairFlip x) =
      TensorProduct.comm ℂ V₁ V₂ (pairTensorEquiv V₁ V₂ x) := by
  rw [pairFlip_eq_transport]
  simp

@[simp]
theorem pairFlip_pairFlip (x : PiTensorProduct ℂ (pairCarrier V₁ V₂)) :
    pairFlip (pairFlip x) = x := by
  apply (pairTensorEquiv V₁ V₂).injective
  rw [pairTensorEquiv_pairFlip, pairTensorEquiv_pairFlip, TensorProduct.comm_comm]

/-- Reversing the order of the factors gives the inverse flip. -/
@[simp]
theorem pairFlip_symm :
    (pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] _).symm =
      (pairFlip : PiTensorProduct ℂ (pairCarrier V₂ V₁) ≃ₗ[ℂ] _) := by
  ext x
  apply (pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] _).injective
  rw [LinearEquiv.apply_symm_apply, pairFlip_pairFlip]

@[simp]
theorem pairFlip_symm_pairTensor (v₁ : V₁) (v₂ : V₂) :
    pairFlip.symm (pairTensor v₂ v₁) = pairTensor v₁ v₂ := by
  rw [pairFlip_symm, pairFlip_pairTensor]

section Actions

variable {F : Type uF} [CommRing F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)

/-- The actual two-block action becomes the binary tensor action. -/
theorem pairTensorEquiv_pairRepresentation (g : (twoBlocks m n hm hn).Levi F)
    (x : PiTensorProduct ℂ (pairCarrier V₁ V₂)) :
    pairTensorEquiv V₁ V₂ (pairRepresentation hm hn π₁ π₂ g x) =
      TensorProduct.map (π₁ (g 0)) (π₂ (g 1)) (pairTensorEquiv V₁ V₂ x) := by
  obtain ⟨y, rfl⟩ := (pairTensorEquiv V₁ V₂).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul v₁ v₂ =>
    simp only [pairTensorEquiv_symm_tmul, pairTensorEquiv_pairTensor, TensorProduct.map_tmul]
    rw [blockTensor_pairTensor hm hn π₁ π₂ g, pairTensorEquiv_pairTensor]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The inverse flip intertwines the swapped actual block actions. -/
theorem pairFlip_symm_pairRepresentation (g : (twoBlocks n m hn hm).Levi F)
    (x : PiTensorProduct ℂ (pairCarrier V₂ V₁)) :
    pairFlip.symm (pairRepresentation hn hm π₂ π₁ g x) =
      pairRepresentation hm hn π₁ π₂ (twoBlockLeviSwap hm hn F g) (pairFlip.symm x) := by
  apply (pairFlip : PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] _).injective
  rw [LinearEquiv.apply_symm_apply, pairFlip_pairRepresentation,
    LinearEquiv.apply_symm_apply]

end Actions

/-- The published multilinear functional is the ordinary tensor functional
composed with the binary tensor coordinates. No finite-dimensional duality is used. -/
theorem pairFunctional_eq_tensor_comp (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    pairFunctional ℓ₁ ℓ₂ =
      (TensorProduct.dualDistrib ℂ V₁ V₂ (ℓ₁ ⊗ₜ[ℂ] ℓ₂)).comp
        (pairTensorEquiv V₁ V₂).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  change pairFunctional ℓ₁ ℓ₂ (PiTensorProduct.tprod ℂ v) =
    TensorProduct.dualDistrib ℂ V₁ V₂ (ℓ₁ ⊗ₜ[ℂ] ℓ₂)
      (pairSplit (pairCarrier V₁ V₂) (PiTensorProduct.tprod ℂ v))
  rw [pairFunctional_tprod, pairSplit_tprod]
  exact (TensorProduct.dualDistrib_apply ℓ₁ ℓ₂ (v 0) (v 1)).symm

/-- Evaluation of the existing functional in binary tensor coordinates. -/
theorem pairFunctional_pairTensorEquiv_symm (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (x : V₁ ⊗[ℂ] V₂) :
    pairFunctional ℓ₁ ℓ₂ ((pairTensorEquiv V₁ V₂).symm x) =
      TensorProduct.dualDistrib ℂ V₁ V₂ (ℓ₁ ⊗ₜ[ℂ] ℓ₂) x := by
  rw [pairFunctional_eq_tensor_comp, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

/-- The inverse flip exchanges the two factor functionals. -/
theorem pairFunctional_pairFlip_symm (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (x : PiTensorProduct ℂ (pairCarrier V₂ V₁)) :
    pairFunctional ℓ₁ ℓ₂ (pairFlip.symm x) = pairFunctional ℓ₂ ℓ₁ x := by
  rw [pairFlip_symm, pairFunctional_pairFlip]

end Langlands.Shahidi
