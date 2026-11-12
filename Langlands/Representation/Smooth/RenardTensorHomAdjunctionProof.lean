import Langlands.Representation.Smooth.RenardTensorHomStatements
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Smooth.SmoothPart.HomDefinitions

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Renard.Smooth

open TensorProduct

universe r u a b c

namespace TensorHom

variable {R : Type r} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type a} {W : Type b} {U : Type c}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable (ρ : Representation R G V) (σ : Representation R G W) (τ : Representation R G U)

omit [IsTopologicalGroup G] in
/-- A smooth linear map from a smooth representation takes smooth values. -/
theorem smooth_value (hρ : IsSmooth ρ) (f : V →ₗ[R] W)
    (hf : f ∈ smoothVectors (Representation.linHom ρ σ)) (x : V) :
    f x ∈ smoothVectors σ := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hρ x
  refine ⟨K ⊓ L, ?_⟩
  intro k
  have hx : ρ (k : G)⁻¹ x = x := hL ⟨(k : G)⁻¹, L.inv_mem k.property.2⟩
  have h := congrArg (fun F : V →ₗ[R] W => F x) (hK ⟨(k : G), k.property.1⟩)
  change σ (k : G) (f (ρ (k : G)⁻¹ x)) = f x at h
  change σ (k : G) (f x) = f x
  simpa only [hx] using h

/-- The ordinary tensor currying equivalence intertwines conjugation actions. -/
def curryEquiv : (Representation.linHom (Representation.tprod ρ σ) τ).Equiv
    (Representation.linHom ρ (Representation.linHom σ τ)) :=
  Representation.Equiv.mk (TensorProduct.lift.equiv (RingHom.id R) V W U).symm (by
    intro g
    ext f x y
    simp [Representation.linHom_apply, Representation.tprod_apply])

/-- An equivariant isomorphism restricts to an isomorphism of smooth parts. -/
def smoothEquiv {ρ : Representation R G V} {σ : Representation R G W}
    (e : ρ.Equiv σ) : (smoothPart ρ).Equiv (smoothPart σ) where
  toLinearEquiv :=
    { toFun := smoothMap e.toIntertwiningMap
      invFun := smoothMap e.symm.toIntertwiningMap
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_add' := (smoothMap e.toIntertwiningMap).map_add
      map_smul' := (smoothMap e.toIntertwiningMap).map_smul }
  isIntertwining' := (smoothMap e.toIntertwiningMap).isIntertwining'

/-- Codomain restriction of a smooth Hom vector, before taking the outer smooth part. -/
def restrictCodomain (hρ : IsSmooth ρ) :
    (smoothPart (Representation.linHom ρ σ)).IntertwiningMap
      (Representation.linHom ρ (smoothPart σ)) where
  toLinearMap :=
    { toFun := fun f => f.val.codRestrict (smoothVectors σ) (smooth_value ρ σ hρ f.val f.property)
      map_add' := by intros; ext x; rfl
      map_smul' := by intros; ext x; rfl }
  isIntertwining' := by
    intro g
    ext f x
    rfl

/-- Postcomposition with the smooth inclusion is equivariant on Hom spaces. -/
def includeCodomain : (Representation.linHom ρ (smoothPart σ)).IntertwiningMap
    (Representation.linHom ρ σ) where
  toLinearMap :=
    { toFun := fun f => (smoothInclusion σ).toLinearMap.comp f
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' := by intros; ext f x; rfl

/-- Smooth Hom from a smooth source is unchanged by taking the codomain smooth part. -/
def smoothCodomainEquiv (hρ : IsSmooth ρ) :
    (smoothPart (Representation.linHom ρ σ)).Equiv
      (smoothPart (Representation.linHom ρ (smoothPart σ))) where
  toLinearEquiv :=
    { toFun := smoothLift (isSmooth_smoothPart _) (restrictCodomain ρ σ hρ)
      invFun := smoothMap (includeCodomain ρ σ)
      left_inv := by intro f; ext x; rfl
      right_inv := by intro f; ext x; rfl
      map_add' := (smoothLift (isSmooth_smoothPart _) (restrictCodomain ρ σ hρ)).map_add
      map_smul' := (smoothLift (isSmooth_smoothPart _) (restrictCodomain ρ σ hρ)).map_smul }
  isIntertwining' :=
    (smoothLift (isSmooth_smoothPart _) (restrictCodomain ρ σ hρ)).isIntertwining'

/-- Currying on smooth Hom, with the inner Hom already restricted to smooth vectors. -/
def smoothCurryEquiv (hρ : IsSmooth ρ) :=
  (smoothEquiv (curryEquiv ρ σ τ)).trans
    (smoothCodomainEquiv ρ (Representation.linHom σ τ) hρ)

/-- The algebraic equivariant tensor–Hom adjunction. -/
def intertwinerCurry : (Representation.tprod ρ σ).IntertwiningMap τ ≃ₗ[R]
    ρ.IntertwiningMap (Representation.linHom σ τ) where
  toFun f :=
    { toLinearMap := TensorProduct.curry f.toLinearMap
      isIntertwining' := by
        intro g
        ext x y
        change f (ρ g x ⊗ₜ y) = τ g (f (x ⊗ₜ σ g⁻¹ y))
        have h := f.isIntertwining _ _ g (x ⊗ₜ σ g⁻¹ y)
        simpa [Representation.tprod_apply] using h }
  invFun f :=
    { toLinearMap := TensorProduct.lift f.toLinearMap
      isIntertwining' := by
        intro g
        ext x y
        have h := congrArg (fun F : W →ₗ[R] U => F (σ g y)) (f.isIntertwining _ _ g x)
        simpa [Representation.linHom_apply, Representation.tprod_apply] using h }
  left_inv f := by ext x y; rfl
  right_inv f := by ext x y; rfl
  map_add' f g := by ext x y; rfl
  map_smul' a f := by ext x y; rfl

/-- The smooth equivariant tensor–Hom adjunction. -/
def smoothIntertwinerCurry (hρ : IsSmooth ρ) :
    (Representation.tprod ρ σ).IntertwiningMap τ ≃ₗ[R]
      ρ.IntertwiningMap (smoothPart (Representation.linHom σ τ)) :=
  (intertwinerCurry ρ σ τ).trans (smoothHomEquiv hρ (Representation.linHom σ τ))

end TensorHom

/-- Renard III.1.15: smooth Hom values, equivariant currying and its invariant form. -/
theorem tensorHomAdjunction : TensorHomAdjunctionStatement.{u, a} := by
  intro G _ _ _ _ _ _ V₁ V₂ V₃ _ _ _ _ _ _ π₁ π₂ π₃
  refine ⟨TensorHom.smooth_value π₁ π₂, ?_⟩
  intro h₁ _ _
  exact ⟨⟨TensorHom.smoothCurryEquiv π₁ π₂ π₃ h₁, fun _ _ _ => rfl⟩,
    ⟨TensorHom.smoothIntertwinerCurry π₁ π₂ π₃ h₁, fun _ _ _ => rfl⟩⟩

end Langlands.Renard.Smooth
