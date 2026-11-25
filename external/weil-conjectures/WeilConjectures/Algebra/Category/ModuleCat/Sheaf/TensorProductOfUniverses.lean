/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Tensor product and scalar extension with independent universes

Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).

The recorded monoidal API requires the site, coefficient and module universes to coincide.
This interface uses the very same tensor product: sectionwise `TensorProduct`, followed by
module sheafification. Ring and module universes are independent. Scalar extension lands
in their maximum, because its first factor is the target ring. The old specialized tensor
and positive-power APIs remain available through the public import.

## Main definitions

- `siteSheafTensorRight`: sheafification of the sectionwise tensor functor.
- `changeOfRingsOfUniverses`: sheafification of sectionwise scalar extension.
- `changeOfRingsHomOfUniverses`: the induced map on scalar extensions.
-/

@[expose] public section

universe v₀ u₀ u m

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

noncomputable local instance {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{m} S) :
    Module S ((ModuleCat.restrictScalars f).obj M) :=
  inferInstanceAs (Module S M)

section ChangeOfRings

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}] [HasWeakSheafify J AddCommGrpCat.{max u m}]

open scoped ChangeOfRings

variable {R₁ R₂ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂)
  (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))

local instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R₁.obj.obj Y)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj.map f).hom).obj
          (M.val.obj Y)) :=
  inferInstanceAs (Module (R₁.obj.obj Y) (M.val.obj Y))

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise tensor restriction exists. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: send `s ⊗ m` to the tensor of the two restrictions. Additivity and the balanced
relation follow from additivity and semilinearity of restrictions and naturality of `α`.
The tensor universal property gives the map, linear over the source section ring. -/
theorem exists_changeOfRingsMapMixedUniverses
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}]
    {R₁ R₂ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂)
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ g : (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)),
      ∀ (s : R₂.obj.obj X) (m : M.val.obj X),
        g (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
          R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m := by
  let : Module (R₁.obj.obj X) (R₂.obj.obj X) :=
    Module.compHom (R₂.obj.obj X) (α.hom.app X).hom
  let : Module (R₁.obj.obj Y) (R₂.obj.obj Y) :=
    Module.compHom (R₂.obj.obj Y) (α.hom.app Y).hom
  let ρ : R₂.obj.obj X →ₛₗ[(R₁.obj.map f).hom] R₂.obj.obj Y :=
    { toFun := R₂.obj.map f
      map_add' := map_add _
      map_smul' := by
        intro r s
        change R₂.obj.map f (α.hom.app X r * s) =
          α.hom.app Y (R₁.obj.map f r) * R₂.obj.map f s
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom (α.hom.naturality f).symm r }
  refine ⟨ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
      ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)))
    { toFun := TensorProduct.map ρ (M.val.restrictₛₗ f)
      map_add' := map_add _
      map_smul' := ?_ }, ?_⟩
  · intro s z
    change TensorProduct (R₁.obj.obj X) (R₂.obj.obj X) (M.val.obj X) at z
    induction z using TensorProduct.inductionOn with
    | tmul t n =>
      change R₂.obj.obj X at t
      change R₂.obj.map f (s * t) ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom]
        M.val.map f n = (R₂.obj.map f s * R₂.obj.map f t) ⊗ₜ[R₁.obj.obj Y,
          (α.hom.app Y).hom] M.val.map f n
      rw [map_mul]
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  · intro s n
    rfl

/-- Restriction on the sectionwise change of rings, characterized on pure tensors.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsMapOfUniverses {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)) :=
  Classical.choose (exists_changeOfRingsMapMixedUniverses α M f)

/-- The restriction map acts on pure tensors by restricting both factors.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: the map is chosen with exactly this formula in exists_changeOfRingsMapMixedUniverses. -/
theorem changeOfRingsMap_tmulOfUniverses {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : R₂.obj.obj X) (m : M.val.obj X) :
    changeOfRingsMapOfUniverses α M f (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
      R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m := by
  exact Classical.choose_spec (exists_changeOfRingsMapMixedUniverses α M f) s m

set_option backward.isDefEq.respectTransparency false in
/-- Identity restriction for change of rings. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: the chosen map sends `s ⊗ m` to `s ⊗ m`, since both restrictions are identities.
The identity comparison has the same action; pure tensors generate the tensor product. -/
theorem changeOfRingsMap_idOfUniverses (X : Cᵒᵖ) :
    changeOfRingsMapOfUniverses α M (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map_id X))).inv.app
          ((ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [changeOfRingsMap_tmulOfUniverses]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Composition of restrictions for change of rings. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: on `s ⊗ m`, both sides restrict each factor first along `f` and then along `g`.
The ring and module presheaf composition laws identify this with restriction along `f ≫ g`.
The scalar comparison acts identically on elements. Tensor generation gives equality. -/
theorem changeOfRingsMap_compOfUniverses {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    changeOfRingsMapOfUniverses α M (f ≫ g) = changeOfRingsMapOfUniverses α M f ≫
      (ModuleCat.restrictScalars ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map f).hom).map
        (changeOfRingsMapOfUniverses α M g) ≫
      (ModuleCat.restrictScalarsComp' ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map f).hom
        ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map g).hom ((R₂.obj ⋙ forget₂ CommRingCat
          RingCat).map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((R₂.obj ⋙ forget₂ CommRingCat RingCat).map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.hom.app Z).hom).obj (M.val.obj Z)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ModuleCat.comp_apply, changeOfRingsMap_tmulOfUniverses]
  change _ = changeOfRingsMapOfUniverses α M g _
  rw [changeOfRingsMap_tmulOfUniverses]
  simp

/-- Sectionwise change of rings with the induced restrictions, before sheafification.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsPresheafOfUniverses : PresheafOfModules.{max u m} (R₂.obj ⋙ forget₂
  CommRingCat RingCat) where
  obj X := (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)
  map f := changeOfRingsMapOfUniverses α M f
  map_id X := changeOfRingsMap_idOfUniverses α M X
  map_comp f g := changeOfRingsMap_compOfUniverses α M f g

/-- Change of rings of a sheaf of modules is the sheafification of sectionwise
extension of scalars, with the target-ring action on the first tensor factor.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsOfUniverses : SheafOfModules.{max u m} ((sheafCompose J (forget₂
  CommRingCat.{u} RingCat.{u})).obj R₂) :=
  (PresheafOfModules.sheafification (𝟙 (R₂.obj ⋙ forget₂ CommRingCat RingCat))).obj
    (changeOfRingsPresheafOfUniverses α M)

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise extension of a module morphism commutes with restrictions.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: on a pure tensor both composites restrict the scalar and apply the original
module morphism to the restricted module section. Naturality of that morphism and
linearity identify the results; pure tensors generate each section tensor product. -/
theorem changeOfRingsHom_naturalityOfUniverses {N : SheafOfModules.{m} ((sheafCompose J (forget₂
  CommRingCat.{u} RingCat.{u})).obj R₁)} (a : M ⟶ N)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (changeOfRingsPresheafOfUniverses α M).map i ≫
      (ModuleCat.restrictScalars (R₂.obj.map i).hom).map
        ((ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)) =
    ((ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)) ≫
      (changeOfRingsPresheafOfUniverses α N).map i := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)
    (changeOfRingsMapOfUniverses α M i _) = changeOfRingsMapOfUniverses α N i
      ((ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U) _)
  rw [changeOfRingsMap_tmulOfUniverses]
  erw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
  rw [changeOfRingsMap_tmulOfUniverses]
  congr 1
  exact PresheafOfModules.naturality_apply a.val i m

/-- Change of rings on module morphisms: sheafify the sectionwise map `id ⊗ a`.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsHomOfUniverses {N : SheafOfModules.{m} ((sheafCompose J (forget₂
  CommRingCat.{u} RingCat.{u})).obj R₁)} (a : M ⟶ N) :
    changeOfRingsOfUniverses α M ⟶ changeOfRingsOfUniverses α N :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R₂)
    (𝟙 (R₂.obj ⋙ forget₂ CommRingCat RingCat))).map
    ({ app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)
       naturality := changeOfRingsHom_naturalityOfUniverses α M a } :
      changeOfRingsPresheafOfUniverses α M ⟶ changeOfRingsPresheafOfUniverses α N)

end ChangeOfRings

section GeneralTensor

variable {C : Type u₀} [Category.{v₀} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance (M : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R.obj Y)
      ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (M.obj Y)) :=
  inferInstanceAs (Module (R.obj Y) (M.obj Y))

/-- Tensor restriction with independent ring and module universes.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteTensorRestriction
    (M N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X) (TensorProduct (R.obj X) (M.obj X) (N.obj X)) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (TensorProduct (R.obj Y) (M.obj Y) (N.obj Y))) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (TensorProduct (R.obj Y) (M.obj Y) (N.obj Y))))
    { toFun := TensorProduct.map (M.restrictₛₗ f) (N.restrictₛₗ f)
      map_add' := map_add _
      map_smul' := (TensorProduct.map (M.restrictₛₗ f) (N.restrictₛₗ f)).map_smulₛₗ }

/-- Tensor restrictions preserve identities.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: both maps fix every pure tensor, and pure tensors generate. -/
theorem siteTensorRestriction_id
    (M N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) (X : Cᵒᵖ) :
    siteTensorRestriction M N (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((R ⋙ forget₂ CommRingCat RingCat).map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map_id X))).inv.app
          (ModuleCat.of (R.obj X) (TensorProduct (R.obj X) (M.obj X) (N.obj X))) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (show M.obj X from M.map (𝟙 X) x) ⊗ₜ[R.obj X]
    (show N.obj X from N.map (𝟙 X) y) = x ⊗ₜ[R.obj X] y
  rw [M.map_id, N.map_id]
  rfl

/-- Tensor restrictions preserve composition.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: evaluate on pure tensors and apply the two module restriction composition laws. -/
theorem siteTensorRestriction_comp
    (M N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    siteTensorRestriction M N (f ≫ g) = siteTensorRestriction M N f ≫
      (ModuleCat.restrictScalars (R.map f).hom).map (siteTensorRestriction M N g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg CommRingCat.Hom.hom (R.map_comp f g))).inv.app
          (ModuleCat.of (R.obj Z) (TensorProduct (R.obj Z) (M.obj Z) (N.obj Z))) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change M.map (f ≫ g) x ⊗ₜ[R.obj Z] N.map (f ≫ g) y =
    M.map g (M.map f x) ⊗ₜ[R.obj Z] N.map g (N.map f y)
  rw [M.map_comp_apply, N.map_comp_apply]

/-- Sectionwise tensor product in arbitrary site, ring and module universes.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteTensorPresheaf
    (M N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (TensorProduct (R.obj X) (M.obj X) (N.obj X))
  map f := siteTensorRestriction M N f
  map_id X := siteTensorRestriction_id M N X
  map_comp f g := siteTensorRestriction_comp M N f g

/-- Tensoring a morphism in the first variable commutes with restrictions.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: on pure tensors this is naturality of the morphism in the first factor. -/
theorem siteTensorHom_naturality
    {M M' : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ M')
    (N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (i : X ⟶ Y) :
    (siteTensorPresheaf M N).map i ≫
        (ModuleCat.restrictScalars (R.map i).hom).map
          (ModuleCat.ofHom (TensorProduct.map (R := R.obj Y) (R₂ := R.obj Y) (f.app Y).hom
            (LinearMap.id : N.obj Y →ₗ[R.obj Y] N.obj Y))) =
      ModuleCat.ofHom (TensorProduct.map (R := R.obj X) (R₂ := R.obj X) (f.app X).hom
            (LinearMap.id : N.obj X →ₗ[R.obj X] N.obj X)) ≫
        (siteTensorPresheaf M' N).map i := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (f.app Y) (M.map i x) ⊗ₜ[R.obj Y] N.map i y =
    M'.map i (f.app X x) ⊗ₜ[R.obj Y] N.map i y
  rw [PresheafOfModules.naturality_apply]

/-- Tensor a morphism with the identity on the second factor.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteTensorHom
    {M M' : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ M')
    (N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf M N ⟶ siteTensorPresheaf M' N where
  app X := ModuleCat.ofHom (TensorProduct.map (R := R.obj X) (R₂ := R.obj X) (f.app X).hom
            (LinearMap.id : N.obj X →ₗ[R.obj X] N.obj X))
  naturality i := siteTensorHom_naturality f N i

/-- Tensoring with a fixed presheaf preserves identity morphisms.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: the map fixes all pure tensors, hence is the identity. -/
theorem siteTensorHom_id
    (M N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorHom (𝟙 M) N = 𝟙 (siteTensorPresheaf M N) := by
  ext X : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Tensoring with a fixed presheaf preserves composites.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: the maps agree on pure tensors by composition in the first factor. -/
theorem siteTensorHom_comp
    {M M' M'' : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : M' ⟶ M'')
    (N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorHom (f ≫ g) N = siteTensorHom f N ≫ siteTensorHom g N := by
  ext X : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- The sectionwise tensor functor with a fixed right factor.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteTensorRight
    (N : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := siteTensorPresheaf M N
  map f := siteTensorHom f N
  map_id M := siteTensorHom_id M N
  map_comp f g := siteTensorHom_comp f g N

/-- The identity coefficient map is locally injective in every module universe.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: its section maps are identity functions, hence injective; use the maximal sieve. -/
theorem siteTensor_identity_locallyInjective {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) : Presheaf.IsLocallyInjective J (𝟙 A.obj) := by
  infer_instance

/-- The identity coefficient map is locally surjective in every module universe.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: every section is already in the image, on the maximal covering sieve. -/
theorem siteTensor_identity_locallySurjective {J : GrothendieckTopology C}
    (A : Sheaf J RingCat.{u}) : Presheaf.IsLocallySurjective J (𝟙 A.obj) := by
  infer_instance

/-- Tensoring module sheaves is forgetting, tensoring sectionwise, then sheafifying.
This formula does not require equality of site, ring and module universes.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def siteSheafTensorRight {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    {A : Sheaf J CommRingCat.{u}}
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
      SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) :=
  letI := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  letI := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  SheafOfModules.forget _ ⋙ siteTensorRight N.val ⋙
    PresheafOfModules.sheafification.{m} (J := J)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj)

end GeneralTensor

end SheafOfModules
