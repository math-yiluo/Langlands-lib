import Langlands.Cohomology.HyperextDegenerationIsotypic
import Langlands.Representation.Category.Subquotients

/-! # Isotypic parts and multiplicity spaces with a commuting group action

For a representation `τ` of a group `G` with a topology, the `τ`-isotypic part of a smooth
representation and its multiplicity space `Hom_G(τ, -)` are functors on smooth representations.
Applied to smooth representations carrying a commuting action of a second group `Γ` (objects of
`Action (SmoothRep R G) Γ`), they give the restricted `Γ`-action on the isotypic part and the
`Γ`-representation on the multiplicity space by composition. The evaluation map
`τ ⊗ Hom_G(τ, V) → V[τ]` is surjective and equivariant for both groups. See
`IsotypicGaloisAction.md`.
-/

noncomputable section

universe uR uG uU uV uΓ

set_option autoImplicit false

namespace Langlands.Shimura.IsotypicGaloisAction

open CategoryTheory TensorProduct
open Langlands.Cohomology.HyperextAbutment
  (isotypicPart isotypicSubrepresentation apply_mem_isotypicPart isotypicPart_le_iff
    intertwiningMap_apply_mem_isotypicPart)

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {U : Type uU} [AddCommGroup U] [Module R U] (τ : Representation R G U)

/-! ## The underlying representation of the second group -/

section Underlying

variable {Γ : Type uΓ} [Group Γ]

/-- The `R`-linear representation of `Γ` on the underlying module of an object of
`Action (SmoothRep R G) Γ`: an element acts by the underlying linear map of its action. -/
def galoisRepresentation (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    Representation R Γ X.V where
  toFun γ := (SmoothRep.hom (X.ρ γ)).toLinearMap
  map_one' := by rw [X.ρ.map_one]; rfl
  map_mul' γ δ := by rw [X.ρ.map_mul]; rfl

@[simp] theorem galoisRepresentation_apply (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) (γ : Γ)
    (v : X.V) : galoisRepresentation X γ v = SmoothRep.hom (X.ρ γ) v :=
  rfl

/-- The two actions on an object of `Action (SmoothRep R G) Γ` commute. -/
theorem galoisRepresentation_commutes (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) (γ : Γ)
    (g : G) (v : X.V) :
    galoisRepresentation X γ (X.V.representation g v) =
      X.V.representation g (galoisRepresentation X γ v) :=
  Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom (X.ρ γ)) g v

/-- A morphism of `Action (SmoothRep R G) Γ` intertwines the underlying `Γ`-representations. -/
theorem galoisRepresentation_naturality {X Y : Action (SmoothRep.{uR, uG, uV} R G) Γ}
    (f : X ⟶ Y) (γ : Γ) (v : X.V) :
    SmoothRep.hom f.hom (galoisRepresentation X γ v) =
      galoisRepresentation Y γ (SmoothRep.hom f.hom v) :=
  congrArg (fun φ : X.V ⟶ Y.V => SmoothRep.hom φ v) (f.comm γ)

end Underlying

/-! ## Isotypic parts -/

section Isotypic

/-- The smooth representation of `G` on the `τ`-isotypic part of a smooth representation `A`:
the sum of the images of all intertwining maps `τ → A`. -/
def isotypicObj (A : SmoothRep.{uR, uG, uV} R G) : SmoothRep.{uR, uG, uV} R G :=
  SmoothRep.subrepresentation A (isotypicSubrepresentation τ A.representation)

/-- An intertwiner `A ⟶ B` restricted to the `τ`-isotypic parts. -/
def isotypicMap {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    isotypicObj τ A ⟶ isotypicObj τ B :=
  SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom f).toLinearMap.restrict
        (fun _ hv => intertwiningMap_apply_mem_isotypicPart τ (SmoothRep.hom f) hv)
      isIntertwining' := fun g => LinearMap.ext fun x : isotypicPart τ A.representation =>
        Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) g x.1) }

@[simp] theorem coe_isotypicMap_apply {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (x : isotypicPart τ A.representation) :
    Subtype.val (SmoothRep.hom (isotypicMap τ f) x) =
      SmoothRep.hom f x.1 :=
  rfl

/-- The `τ`-isotypic part as a functor on smooth representations. -/
def isotypicFunctor : SmoothRep.{uR, uG, uV} R G ⥤ SmoothRep.{uR, uG, uV} R G where
  obj := isotypicObj τ
  map := isotypicMap τ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem isotypicFunctor_obj (A : SmoothRep.{uR, uG, uV} R G) :
    (isotypicFunctor τ).obj A = isotypicObj τ A :=
  rfl

/-- The inclusion of the `τ`-isotypic part, natural in the smooth representation. -/
def isotypicι : isotypicFunctor.{uR, uG, uU, uV} τ ⟶ 𝟭 (SmoothRep.{uR, uG, uV} R G) where
  app A := SmoothRep.subtype A (isotypicSubrepresentation τ A.representation)
  naturality _ _ _ := rfl

@[simp] theorem isotypicι_app_apply (A : SmoothRep.{uR, uG, uV} R G)
    (x : isotypicPart τ A.representation) :
    SmoothRep.hom ((isotypicι τ).app A) x = x.1 :=
  rfl

theorem isotypicι_app_injective (A : SmoothRep.{uR, uG, uV} R G) :
    Function.Injective (SmoothRep.hom ((isotypicι τ).app A)) :=
  SmoothRep.subtype_injective A _

instance (A : SmoothRep.{uR, uG, uV} R G) : Mono ((isotypicι τ).app A) :=
  ⟨fun a b h => ObjectProperty.hom_ext (Langlands.smoothRepProperty R G) (by
    ext x
    exact isotypicι_app_injective τ A
      (congrArg (fun φ => SmoothRep.hom φ x) h))⟩

variable (Γ : Type uΓ) [Group Γ]

/-- The `τ`-isotypic part of a smooth representation of `G` with a commuting `Γ`-action, with
the restricted actions of both groups. -/
def isotypicActionFunctor :
    Action (SmoothRep.{uR, uG, uV} R G) Γ ⥤ Action (SmoothRep.{uR, uG, uV} R G) Γ :=
  (isotypicFunctor τ).mapAction Γ

@[simp] theorem isotypicActionFunctor_obj_V (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    ((isotypicActionFunctor τ Γ).obj X).V = isotypicObj τ X.V :=
  rfl

theorem isotypicActionFunctor_obj_ρ (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) (γ : Γ) :
    ((isotypicActionFunctor τ Γ).obj X).ρ γ = isotypicMap τ (X.ρ γ) :=
  rfl

/-- The inclusion of the `τ`-isotypic part, equivariant for both groups and natural. -/
def isotypicActionι :
    isotypicActionFunctor.{uR, uG, uU, uV} τ Γ ⟶ 𝟭 (Action (SmoothRep.{uR, uG, uV} R G) Γ) where
  app X := ⟨(isotypicι τ).app X.V, fun γ => (isotypicι τ).naturality (X.ρ γ)⟩
  naturality _ _ f := Action.hom_ext _ _ ((isotypicι τ).naturality f.hom)

@[simp] theorem isotypicActionι_app_hom (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    ((isotypicActionι τ Γ).app X).hom = (isotypicι τ).app X.V :=
  rfl

/-- The representation of `Γ` on the `τ`-isotypic part, restricted from the action on the
ambient module. -/
def isotypicGaloisRepresentation (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    Representation R Γ (isotypicPart τ X.V.representation) :=
  galoisRepresentation ((isotypicActionFunctor τ Γ).obj X)

@[simp] theorem coe_isotypicGaloisRepresentation_apply
    (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) (γ : Γ) (x : isotypicPart τ X.V.representation) :
    (isotypicGaloisRepresentation τ Γ X γ x : X.V) = galoisRepresentation X γ x :=
  rfl

end Isotypic

/-! ## Multiplicity spaces -/

section Multiplicity

/-- The multiplicity space `Hom_G(τ, A)` of intertwining maps as an `R`-module, functorial in the
smooth representation `A` by composition. -/
def multiplicityFunctor : SmoothRep.{uR, uG, uV} R G ⥤ ModuleCat.{max uU uV} R where
  obj A := ModuleCat.of R (τ.IntertwiningMap A.representation)
  map f := ModuleCat.ofHom (Representation.IntertwiningMap.llcomp _ _ _ (SmoothRep.hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem multiplicityFunctor_map_apply {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (φ : τ.IntertwiningMap A.representation) :
    ((multiplicityFunctor τ).map f).hom φ = (SmoothRep.hom f).comp φ :=
  rfl

variable (Γ : Type uΓ) [Group Γ]

/-- The multiplicity spaces of a smooth representation with a commuting `Γ`-action, with `Γ`
acting by composition with its action. -/
def multiplicityActionFunctor :
    Action (SmoothRep.{uR, uG, uV} R G) Γ ⥤ Action (ModuleCat.{max uU uV} R) Γ :=
  (multiplicityFunctor τ).mapAction Γ

/-- The multiplicity spaces as `R`-linear representations of `Γ`. -/
def multiplicityRepFunctor :
    Action (SmoothRep.{uR, uG, uV} R G) Γ ⥤ Rep.{max uU uV} R Γ :=
  multiplicityActionFunctor τ Γ ⋙ Rep.ActionToRep R Γ

/-- The representation of `Γ` on `Hom_G(τ, X)` by composition with the action of `Γ` on `X`. -/
def multiplicityRepresentation (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) :
    Representation R Γ (τ.IntertwiningMap X.V.representation) :=
  ((multiplicityRepFunctor τ Γ).obj X).ρ

@[simp] theorem multiplicityRepresentation_apply (X : Action (SmoothRep.{uR, uG, uV} R G) Γ)
    (γ : Γ) (φ : τ.IntertwiningMap X.V.representation) :
    multiplicityRepresentation τ Γ X γ φ = (SmoothRep.hom (X.ρ γ)).comp φ :=
  rfl

end Multiplicity

/-! ## The evaluation map -/

section Evaluation

/-- Evaluation `u ⊗ φ ↦ φ u` from `τ ⊗ Hom_G(τ, A)` to the `τ`-isotypic part of `A`. -/
def isotypicEvaluation (A : SmoothRep.{uR, uG, uV} R G) :
    U ⊗[R] τ.IntertwiningMap A.representation →ₗ[R] isotypicPart τ A.representation :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun φ => ⟨φ u, apply_mem_isotypicPart φ u⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := fun u u' => LinearMap.ext fun φ => Subtype.ext (map_add φ u u')
      map_smul' := fun c u => LinearMap.ext fun φ => Subtype.ext (map_smul φ c u) }

@[simp] theorem coe_isotypicEvaluation_tmul (A : SmoothRep.{uR, uG, uV} R G) (u : U)
    (φ : τ.IntertwiningMap A.representation) :
    (isotypicEvaluation τ A (u ⊗ₜ φ) : A) = φ u := by
  rw [isotypicEvaluation, TensorProduct.lift.tmul]
  rfl

/-- Every vector of the `τ`-isotypic part is a sum of values of intertwining maps `τ → A`. -/
theorem isotypicEvaluation_surjective (A : SmoothRep.{uR, uG, uV} R G) :
    Function.Surjective (isotypicEvaluation τ A) := by
  rintro ⟨x, hx⟩
  have key : isotypicPart τ A.representation ≤
      (LinearMap.range (isotypicEvaluation τ A)).map (isotypicPart τ A.representation).subtype :=
    (isotypicPart_le_iff τ A.representation).2 fun φ u =>
      ⟨_, LinearMap.mem_range_self _ (u ⊗ₜ φ), coe_isotypicEvaluation_tmul τ A u φ⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := key hx
  exact ⟨t, Subtype.ext ht⟩

/-- Evaluation intertwines the action of `G` on the first factor with its action on `A`. -/
theorem isotypicEvaluation_map_tmul (A : SmoothRep.{uR, uG, uV} R G) (g : G) (u : U)
    (φ : τ.IntertwiningMap A.representation) :
    isotypicEvaluation τ A (τ g u ⊗ₜ φ) =
      (isotypicObj τ A).representation g (isotypicEvaluation τ A (u ⊗ₜ φ)) := by
  refine Subtype.ext ?_
  change ((isotypicEvaluation τ A (τ g u ⊗ₜ φ) : isotypicPart τ A.representation) : A) =
    A.representation g (isotypicEvaluation τ A (u ⊗ₜ φ) : isotypicPart τ A.representation)
  rw [coe_isotypicEvaluation_tmul, coe_isotypicEvaluation_tmul]
  exact Representation.IntertwiningMap.isIntertwining _ _ φ g u

variable (Γ : Type uΓ) [Group Γ]

/-- Evaluation intertwines the action of `Γ` on the multiplicity space with its action on the
isotypic part. -/
theorem isotypicEvaluation_galois (X : Action (SmoothRep.{uR, uG, uV} R G) Γ) (γ : Γ) :
    isotypicEvaluation τ X.V ∘ₗ
        (LinearMap.lTensor U (multiplicityRepresentation τ Γ X γ)) =
      isotypicGaloisRepresentation τ Γ X γ ∘ₗ isotypicEvaluation τ X.V := by
  refine TensorProduct.ext' fun u φ => Subtype.ext ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    coe_isotypicEvaluation_tmul, coe_isotypicGaloisRepresentation_apply,
    coe_isotypicEvaluation_tmul, multiplicityRepresentation_apply]
  rfl

end Evaluation

end Langlands.Shimura.IsotypicGaloisAction
