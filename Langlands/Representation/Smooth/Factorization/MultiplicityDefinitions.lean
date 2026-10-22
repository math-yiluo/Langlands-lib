import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Intertwining

/-!
# Multiplicity representation and tensor evaluation for a product group

For a complex representation `ρ` of `G₁ × G₂` and a complex representation `σ`
of `G₁`, the space of `G₁`-intertwiners from `σ` to the restriction
`ρ.comp (MonoidHom.inl G₁ G₂)` carries a representation of `G₂` by
postcomposition with `ρ (1, g₂)`. Evaluation `s ⊗ f ↦ f s` is an intertwiner
from the external tensor of `σ` and this multiplicity representation to `ρ`.
No smoothness, admissibility or irreducibility is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.TwoFactorExistence

open Representation

universe uG₁ uG₂ uV

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V)

/-- The restriction of a representation of `G₁ × G₂` to the first factor. -/
def first : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂)

/-- The restriction of a representation of `G₁ × G₂` to the second factor. -/
def second : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂)

theorem first_apply (g : G₁) (v : V) : first ρ g v = ρ (g, 1) v := rfl

theorem second_apply (g : G₂) (v : V) : second ρ g v = ρ (1, g) v := rfl

theorem second_first_apply (g : G₁ × G₂) (v : V) :
    second ρ g.2 (first ρ g.1 v) = ρ g v := by
  have h : ((1 : G₁), g.2) * (g.1, (1 : G₂)) = g := by ext <;> simp
  rw [first_apply, second_apply, ← Module.End.mul_apply, ← map_mul, h]

theorem first_second_apply (g : G₁ × G₂) (v : V) :
    first ρ g.1 (second ρ g.2 v) = ρ g v := by
  have h : (g.1, (1 : G₂)) * ((1 : G₁), g.2) = g := by ext <;> simp
  rw [first_apply, second_apply, ← Module.End.mul_apply, ← map_mul, h]

theorem first_second_comm (g₁ : G₁) (g₂ : G₂) (v : V) :
    first ρ g₁ (second ρ g₂ v) = second ρ g₂ (first ρ g₁ v) := by
  rw [first_second_apply ρ (g₁, g₂), second_first_apply ρ (g₁, g₂)]

theorem first_mul_apply (g h : G₁) (v : V) :
    first ρ g (first ρ h v) = first ρ (g * h) v := by
  rw [map_mul, Module.End.mul_apply]

/-- The action of an element of the second factor, as an endomorphism of the
restriction to the first factor. -/
def secondOp (g : G₂) : (first ρ).IntertwiningMap (first ρ) where
  toLinearMap := second ρ g
  isIntertwining' h := by
    ext v
    exact (first_second_comm ρ h g v).symm

end Langlands.TwoFactorExistence

namespace Langlands.ProductFactorization

universe uG uG₁ uG₂ uS uV uW

open Representation

section Product

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V)

@[simp]
theorem secondFactorIntertwiner_apply (g₂ : G₂) (v : V) :
    TwoFactorExistence.secondOp ρ g₂ v = ρ (1, g₂) v :=
  rfl

variable {S : Type uS} [AddCommGroup S] [Module ℂ S] (σ : Representation ℂ G₁ S)

/-- The multiplicity representation of `G₂` on the space of `G₁`-intertwiners
`σ → ρ|G₁`: the element `g₂` sends `f` to `s ↦ ρ (1, g₂) (f s)`. Each operator
is Mathlib's linear postcomposition `IntertwiningMap.llcomp` with
`TwoFactorExistence.secondOp ρ g₂`. -/
def multiplicityRepresentation :
    Representation ℂ G₂ (σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))) where
  toFun g₂ := IntertwiningMap.llcomp σ (ρ.comp (MonoidHom.inl G₁ G₂))
    (ρ.comp (MonoidHom.inl G₁ G₂)) (TwoFactorExistence.secondOp ρ g₂)
  map_one' := by
    ext f s
    change ρ (1, 1) (f s) = f s
    rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  map_mul' g h := by
    ext f s
    change ρ (1, g * h) (f s) = ρ (1, g) (ρ (1, h) (f s))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

/-- The defining action law of the multiplicity representation. -/
@[simp]
theorem multiplicityRepresentation_apply_apply (g₂ : G₂)
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))) (s : S) :
    multiplicityRepresentation ρ σ g₂ f s = ρ (1, g₂) (f s) :=
  rfl

/-- The multiplicity action is composition with `TwoFactorExistence.secondOp`. -/
theorem multiplicityRepresentation_apply (g₂ : G₂)
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))) :
    multiplicityRepresentation ρ σ g₂ f = (TwoFactorExistence.secondOp ρ g₂).comp f :=
  rfl

/-- Tensor evaluation `s ⊗ f ↦ f s`, from the external tensor of `σ` and the
multiplicity representation to `ρ`. Its linear map is
`TensorProduct.lift` of the flipped bilinear evaluation
`(IntertwiningMap.toLinearMapl _ _).flip`. -/
def multiplicityEvaluation :
    (Representation.tprod (σ.comp (MonoidHom.fst G₁ G₂))
      ((multiplicityRepresentation ρ σ).comp (MonoidHom.snd G₁ G₂))).IntertwiningMap ρ where
  toLinearMap := TensorProduct.lift
    (IntertwiningMap.toLinearMapl σ (ρ.comp (MonoidHom.inl G₁ G₂))).flip
  isIntertwining' g := by
    obtain ⟨g₁, g₂⟩ := g
    apply TensorProduct.ext'
    intro s f
    change ρ (1, g₂) (f (σ g₁ s)) = ρ (g₁, g₂) (f s)
    rw [IntertwiningMap.isIntertwining σ (ρ.comp (MonoidHom.inl G₁ G₂)) f g₁ s]
    change ρ (1, g₂) (ρ (g₁, 1) (f s)) = ρ (g₁, g₂) (f s)
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

/-- The pure-tensor evaluation formula. -/
@[simp]
theorem multiplicityEvaluation_tmul (s : S)
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl G₁ G₂))) :
    multiplicityEvaluation ρ σ (s ⊗ₜ[ℂ] f) = f s :=
  rfl

/-- The linear map underlying `multiplicityEvaluation`. -/
theorem multiplicityEvaluation_toLinearMap :
    (multiplicityEvaluation ρ σ).toLinearMap = TensorProduct.lift
      (IntertwiningMap.toLinearMapl σ (ρ.comp (MonoidHom.inl G₁ G₂))).flip :=
  rfl

end Product

section Subrepresentation

variable {G : Type uG} [Monoid G] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {τ : Representation ℂ G W}

/-- The inclusion of a subrepresentation, as an intertwiner from its
representation `S₀.toRepresentation` to the ambient representation. Its linear
map is the submodule inclusion `S₀.toSubmodule.subtype`. -/
def subrepresentationInclusion (S₀ : Subrepresentation τ) :
    S₀.toRepresentation.IntertwiningMap τ where
  toLinearMap := S₀.toSubmodule.subtype
  isIntertwining' _ := by
    ext v
    rfl

@[simp]
theorem subrepresentationInclusion_apply (S₀ : Subrepresentation τ) (v : S₀.toSubmodule) :
    subrepresentationInclusion S₀ v = (v : W) :=
  rfl

theorem subrepresentationInclusion_injective (S₀ : Subrepresentation τ) :
    Function.Injective (subrepresentationInclusion S₀) :=
  Subtype.val_injective

end Subrepresentation

/-- Evaluation at the inclusion of a subrepresentation of the restriction to
`G₁` returns the vector itself. -/
theorem multiplicityEvaluation_tmul_subrepresentationInclusion
    {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V)
    (S₀ : Subrepresentation (ρ.comp (MonoidHom.inl G₁ G₂))) (v : S₀.toSubmodule) :
    multiplicityEvaluation ρ S₀.toRepresentation (v ⊗ₜ[ℂ] subrepresentationInclusion S₀) =
      (v : V) :=
  rfl

end Langlands.ProductFactorization
