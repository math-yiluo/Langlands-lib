import Langlands.Automorphic.ArchimedeanMultiplicityActions

/-! # Compact and Lie structures on residual multiplicities -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.GKTensorEvaluation

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV uW uH uJ

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
  (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)

local instance gkResidualStructuresGroup : AddCommGroup (Multiplicity ρ π ρ' π') :=
  (gkHoms ρ π ρ' π').addCommGroup

/-- Every commuting group representation acts on the residual multiplicities. -/
def postcomposeRepresentation {H : Type uH} [Group H] (σ : Representation ℂ H W)
    (hk : ∀ h k w, σ h (ρ' k w) = ρ' k (σ h w))
    (hl : ∀ h X w, σ h (π' X w) = π' X (σ h w)) :
    Representation ℂ H (Multiplicity ρ π ρ' π') where
  toFun h := postcompose ρ π ρ' π' (σ h) (hk h) (hl h)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change σ 1 (f.val v) = f.val v
    exact congrArg (fun T : Module.End ℂ W => T (f.val v)) (map_one σ)
  map_mul' h h' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change σ (h * h') (f.val v) = σ h (σ h' (f.val v))
    exact congrArg (fun T : Module.End ℂ W => T (f.val v)) (map_mul σ h h')

@[simp]
theorem postcomposeRepresentation_apply {H : Type uH} [Group H] (σ : Representation ℂ H W)
    (hk : ∀ h k w, σ h (ρ' k w) = ρ' k (σ h w))
    (hl : ∀ h X w, σ h (π' X w) = π' X (σ h w))
    (h : H) (f : Multiplicity ρ π ρ' π') (v : V) :
    (postcomposeRepresentation ρ π ρ' π' σ hk hl h f).val v = σ h (f.val v) := rfl

/-- Every commuting complex Lie action acts on the same residual multiplicities. -/
def postcomposeLie {J : Type uJ} [LieRing J] [LieAlgebra ℂ J]
    (ψ : J →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hk : ∀ X k w, ψ X (ρ' k w) = ρ' k (ψ X w))
    (hl : ∀ X Y w, ψ X (π' Y w) = π' Y (ψ X w)) :
    J →ₗ⁅ℂ⁆ Module.End ℂ (Multiplicity ρ π ρ' π') where
  toFun X := postcompose ρ π ρ' π' (ψ X) (hk X) (hl X)
  map_add' X Y := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : Module.End ℂ W => T (f.val v)) (map_add ψ X Y)
  map_smul' c X := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : Module.End ℂ W => T (f.val v)) (map_smul ψ c X)
  map_lie' := by
    intro X Y
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : Module.End ℂ W => T (f.val v)) (ψ.map_lie X Y)

@[simp]
theorem postcomposeLie_apply {J : Type uJ} [LieRing J] [LieAlgebra ℂ J]
    (ψ : J →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hk : ∀ X k w, ψ X (ρ' k w) = ρ' k (ψ X w))
    (hl : ∀ X Y w, ψ X (π' Y w) = π' Y (ψ X w))
    (X : J) (f : Multiplicity ρ π ρ' π') (v : V) :
    (postcomposeLie ρ π ρ' π' ψ hk hl X f).val v = ψ X (f.val v) := rfl

/-- Commutation of two remaining operators is retained by residual postcomposition. -/
theorem postcompose_commute (T U : Module.End ℂ W)
    (hTk : ∀ k w, T (ρ' k w) = ρ' k (T w))
    (hTl : ∀ X w, T (π' X w) = π' X (T w))
    (hUk : ∀ k w, U (ρ' k w) = ρ' k (U w))
    (hUl : ∀ X w, U (π' X w) = π' X (U w))
    (hTU : ∀ w, T (U w) = U (T w)) (f : Multiplicity ρ π ρ' π') :
    postcompose ρ π ρ' π' T hTk hTl (postcompose ρ π ρ' π' U hUk hUl f) =
      postcompose ρ π ρ' π' U hUk hUl (postcompose ρ π ρ' π' T hTk hTl f) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  exact hTU (f.val v)

theorem evaluation_postcomposeRepresentation {H : Type uH} [Group H]
    (σ : Representation ℂ H W)
    (hk : ∀ h k w, σ h (ρ' k w) = ρ' k (σ h w))
    (hl : ∀ h X w, σ h (π' X w) = π' X (σ h w))
    (h : H) (t : V ⊗[ℂ] Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π'
        (TensorProduct.map LinearMap.id (postcomposeRepresentation ρ π ρ' π' σ hk hl h) t) =
      σ h (evaluation ρ π ρ' π' t) :=
  evaluation_postcompose ρ π ρ' π' (σ h) (hk h) (hl h) t

theorem evaluation_postcomposeLie {J : Type uJ} [LieRing J] [LieAlgebra ℂ J]
    (ψ : J →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hk : ∀ X k w, ψ X (ρ' k w) = ρ' k (ψ X w))
    (hl : ∀ X Y w, ψ X (π' Y w) = π' Y (ψ X w))
    (X : J) (t : V ⊗[ℂ] Multiplicity ρ π ρ' π') :
    evaluation ρ π ρ' π'
        (TensorProduct.map LinearMap.id (postcomposeLie ρ π ρ' π' ψ hk hl X) t) =
      ψ X (evaluation ρ π ρ' π' t) :=
  evaluation_postcompose ρ π ρ' π' (ψ X) (hk X) (hl X) t

end Langlands.Archimedean.GKTensorEvaluation
