/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Abelian sheaves with an action of a ring as sheaves of modules

Let `Λ` be a commutative ring. An abelian sheaf `F` together with a ring homomorphism
`Λ →+* End F` is canonically a sheaf of `Λ`-modules. In this file, we do this functorially: a
functor `P : 𝒜 ⥤ Sheaf J AddCommGrpCat` with an action `ρ a : Λ →+* End (P.obj a)` natural in
`a` lifts along the forgetful functor
`sheafCompose J (forget₂ (ModuleCat Λ) AddCommGrpCat)`.

## Main definitions and results

- `ModuleCat.coindAddCommGrp Λ`: coinduction `Hom_ℤ(Λ, -)` from abelian groups to `Λ`-modules,
  right adjoint to the forgetful functor (`ModuleCat.forget₂CoindAddCommGrpAdj`).
- `CategoryTheory.Sheaf.moduleLift P ρ hρ : 𝒜 ⥤ Sheaf J (ModuleCat Λ)`: the lift of `P`, with
  `CategoryTheory.Sheaf.moduleLift_comp_sheafCompose` (this holds by `rfl`).
- The lift is additive, preserves finite limits, finite colimits, reflects isomorphisms or is
  faithful as soon as `P` is (does). For finite colimits, we use that the forgetful functor on
  sheaves is a left adjoint, because `forget₂` is (its right adjoint being coinduction).
- The main example: for a commutative ring object `R` of abelian sheaves and a ring
  homomorphism `φ : Λ →+* Γ R`, the forgetful functor from `R`-module objects lifts to sheaves
  of `Λ`-modules, through the action `CategoryTheory.Mod.sectionActRingHom` of global sections.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace ModuleCat

variable (Λ : Type w) [Ring Λ]

/-- Coinduction from abelian groups to `Λ`-modules, `A ↦ Hom_ℤ(Λ, A)`. -/
noncomputable def coindAddCommGrp : AddCommGrpCat.{w} ⥤ ModuleCat.{w} Λ :=
  (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse ⋙
    ModuleCat.coextendScalars (algebraMap ℤ Λ)

/-- The forgetful functor from `Λ`-modules to abelian groups is left adjoint to coinduction. -/
noncomputable def forget₂CoindAddCommGrpAdj :
    forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⊣ coindAddCommGrp Λ :=
  ((ModuleCat.restrictCoextendScalarsAdj.{w} (algebraMap ℤ Λ)).comp
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.toAdjunction).ofNatIsoLeft
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))

instance : (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).IsLeftAdjoint :=
  (forget₂CoindAddCommGrpAdj Λ).isLeftAdjoint

instance : (coindAddCommGrp Λ).IsRightAdjoint :=
  (forget₂CoindAddCommGrpAdj Λ).isRightAdjoint

end ModuleCat

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The ring homomorphism from the endomorphisms of an abelian sheaf to the additive
endomorphisms of its sections over `U`. -/
noncomputable def sectionsEndRingHom (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    End F →+* AddMonoid.End (F.obj.obj U) where
  toFun f := (f.asHom.hom.app U).hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {Λ : Type w} [CommRing Λ]

/-- The sections over `U` of an abelian sheaf `F` with an action `Λ →+* End F`, as a
`Λ`-module. -/
noncomputable abbrev sectionsModule (F : Sheaf J AddCommGrpCat.{w}) (r : Λ →+* End F) (U : Cᵒᵖ) :
    ModuleCat.{w} Λ :=
  letI := Module.compHom (F.obj.obj U) ((sectionsEndRingHom F U).comp r)
  ModuleCat.of Λ (F.obj.obj U)

/-- A morphism of abelian sheaves with an action of `Λ`, commuting with the action, induces
`Λ`-linear maps on sections. -/
noncomputable def sectionsModuleMap {F G : Sheaf J AddCommGrpCat.{w}} (r : Λ →+* End F)
    (r' : Λ →+* End G) (f : F ⟶ G) (hf : ∀ c, (r c).asHom ≫ f = f ≫ (r' c).asHom)
    (U : Cᵒᵖ) :
    sectionsModule F r U ⟶ sectionsModule G r' U :=
  letI := Module.compHom (F.obj.obj U) ((sectionsEndRingHom F U).comp r)
  letI := Module.compHom (G.obj.obj U) ((sectionsEndRingHom G U).comp r')
  ModuleCat.ofHom
    { toFun := f.hom.app U
      map_add' := (f.hom.app U).hom.map_add
      map_smul' := fun c x ↦ by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (congr_arg (fun g : F ⟶ G ↦ g.hom) (hf c)) U) x }

@[simp]
lemma sectionsModuleMap_apply {F G : Sheaf J AddCommGrpCat.{w}} (r : Λ →+* End F)
    (r' : Λ →+* End G) (f : F ⟶ G) (hf : ∀ c, (r c).asHom ≫ f = f ≫ (r' c).asHom)
    (U : Cᵒᵖ)
    (x : F.obj.obj U) : sectionsModuleMap r r' f hf U x = f.hom.app U x :=
  rfl

/-- The presheaf of `Λ`-modules underlying an abelian sheaf `F` with an action `Λ →+* End F`. -/
noncomputable def modulePresheaf (F : Sheaf J AddCommGrpCat.{w}) (r : Λ →+* End F) :
    Cᵒᵖ ⥤ ModuleCat.{w} Λ where
  obj U := sectionsModule F r U
  map {U V} g :=
    letI := Module.compHom (F.obj.obj U) ((sectionsEndRingHom F U).comp r)
    letI := Module.compHom (F.obj.obj V) ((sectionsEndRingHom F V).comp r)
    ModuleCat.ofHom
      { toFun := F.obj.map g
        map_add' := (F.obj.map g).hom.map_add
        map_smul' := fun c x ↦
          (ConcreteCategory.congr_hom ((r c).asHom.hom.naturality g) x).symm }
  map_id U := ConcreteCategory.hom_ext _ _ fun x ↦
    ConcreteCategory.congr_hom (F.obj.map_id U) x
  map_comp f g := ConcreteCategory.hom_ext _ _ fun x ↦
    ConcreteCategory.congr_hom (F.obj.map_comp f g) x

variable {𝒜 : Type*} [Category* 𝒜] (P : 𝒜 ⥤ Sheaf J AddCommGrpCat.{w})
  (ρ : ∀ a, Λ →+* End (P.obj a))
  (hρ : ∀ {a b : 𝒜} (f : a ⟶ b) (c : Λ),
    (ρ a c).asHom ≫ P.map f = P.map f ≫ (ρ b c).asHom)

/-- A functor `P : 𝒜 ⥤ Sheaf J AddCommGrpCat` with an action `ρ a : Λ →+* End (P.obj a)`
natural in `a` lifts to sheaves of `Λ`-modules. -/
noncomputable def moduleLift : 𝒜 ⥤ Sheaf J (ModuleCat.{w} Λ) where
  obj a := ⟨modulePresheaf (P.obj a) (ρ a),
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ _ AddCommGrpCat.{w}) (P.obj a).property⟩
  map f :=
    { hom :=
        { app := sectionsModuleMap (ρ _) (ρ _) (P.map f) (hρ f)
          naturality U V g := by
            ext x
            exact ConcreteCategory.congr_hom ((P.map f).hom.naturality g) x } }
  map_id a := by
    ext U x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congr_arg (fun f : P.obj a ⟶ P.obj a ↦ f.hom) (P.map_id a)) U) x
  map_comp f g := by
    ext U x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congr_arg (fun f : P.obj _ ⟶ P.obj _ ↦ f.hom) (P.map_comp f g)) U) x

@[simp]
lemma moduleLift_obj_obj_obj (a : 𝒜) (U : Cᵒᵖ) :
    (forget₂ _ AddCommGrpCat.{w}).obj (((moduleLift P ρ hρ).obj a).obj.obj U) =
      (P.obj a).obj.obj U :=
  rfl

lemma moduleLift_obj_obj_smul (a : 𝒜) (U : Cᵒᵖ) (c : Λ)
    (x : ((moduleLift P ρ hρ).obj a).obj.obj U) :
    c • x = (ρ a c).asHom.hom.app U x :=
  rfl


@[simp]
lemma moduleLift_map_hom_app_apply {a b : 𝒜} (f : a ⟶ b) (U : Cᵒᵖ)
    (x : (P.obj a).obj.obj U) :
    ((moduleLift P ρ hρ).map f).hom.app U x = (P.map f).hom.app U x :=
  rfl

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The lift `moduleLift P ρ hρ` composed with the forgetful functor is `P`. -/
noncomputable def moduleLiftCompIso :
    moduleLift P ρ hρ ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w}) ≅ P :=
  Iso.refl _

@[simp]
lemma moduleLiftCompIso_hom_app (a : 𝒜) :
    (moduleLiftCompIso P ρ hρ).hom.app a = 𝟙 (P.obj a) :=
  rfl

@[simp]
lemma moduleLiftCompIso_inv_app (a : 𝒜) :
    (moduleLiftCompIso P ρ hρ).inv.app a = 𝟙 (P.obj a) :=
  rfl

/-- The lift `moduleLift P ρ hρ` composed with the forgetful functor is equal to `P`. -/
lemma moduleLift_comp_sheafCompose :
    moduleLift P ρ hρ ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w}) = P :=
  rfl

/-- `moduleLift P ρ hρ` maps a morphism to an isomorphism if and only if `P` does. -/
lemma isIso_moduleLift_map_iff {a b : 𝒜} (f : a ⟶ b) :
    IsIso ((moduleLift P ρ hρ).map f) ↔ IsIso (P.map f) :=
  ⟨fun _ ↦ inferInstanceAs
      (IsIso ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
        ((moduleLift P ρ hρ).map f))),
    fun _ ↦ by
      have : IsIso ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
          ((moduleLift P ρ hρ).map f)) := inferInstanceAs (IsIso (P.map f))
      exact isIso_of_reflects_iso _ (sheafCompose J (forget₂ _ AddCommGrpCat.{w}))⟩

instance [P.ReflectsIsomorphisms] : (moduleLift P ρ hρ).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso (P.map f) := (isIso_moduleLift_map_iff P ρ hρ f).1 inferInstance
    exact isIso_of_reflects_iso f P

instance [P.Faithful] : (moduleLift P ρ hρ).Faithful :=
  Functor.Faithful.of_comp_iso (moduleLiftCompIso P ρ hρ)

instance [Preadditive 𝒜] [P.Additive] : (moduleLift P ρ hρ).Additive where
  map_add {a b f g} := by
    ext U x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congr_arg (fun f : P.obj a ⟶ P.obj b ↦ f.hom)
        (P.map_add (f := f) (g := g))) U) x

/-- The forgetful functor from sheaves of `Λ`-modules to abelian sheaves preserves finite
limits. -/
instance preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
        sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{w} Λ) _)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance [PreservesFiniteLimits P] : PreservesFiniteLimits (moduleLift P ρ hρ) := by
  have : PreservesFiniteLimits
      (moduleLift P ρ hρ ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w})) :=
    inferInstanceAs (PreservesFiniteLimits P)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))

/-- The forgetful functor from sheaves of `Λ`-modules to abelian sheaves is a left adjoint,
since `forget₂` is a left adjoint and commutes with sheafification. -/
instance isLeftAdjoint_sheafCompose_forget₂ [HasWeakSheafify J AddCommGrpCat.{w}] :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso
    (Functor.isoWhiskerLeft (sheafCompose J (forget₂ _ AddCommGrpCat.{w}))
      (sheafificationNatIso J AddCommGrpCat.{w}).symm ≪≫
      Functor.rightUnitor _ :
      Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{w} Λ) _) ≅ _)

instance [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (ModuleCat.{w} Λ)]
    [PreservesFiniteColimits P] : PreservesFiniteColimits (moduleLift P ρ hρ) := by
  have : PreservesFiniteColimits
      (moduleLift P ρ hρ ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w})) :=
    inferInstanceAs (PreservesFiniteColimits P)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))

end Sheaf

end CategoryTheory

section Example

open AlgebraicGeometry CategoryTheory MonObj

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
  [IsCommMonObj R] (Λ : Type (u + 1)) [CommRing Λ] (φ : Λ →+* Γ R)

noncomputable example : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  Sheaf.moduleLift (Mod.forget R) (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))

example : (Sheaf.moduleLift (Λ := Λ) (Mod.forget R) (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))).Additive := inferInstance

example : PreservesFiniteLimits (Sheaf.moduleLift (Λ := Λ) (Mod.forget R)
    (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))) := inferInstance

example : PreservesFiniteColimits (Sheaf.moduleLift (Λ := Λ) (Mod.forget R)
    (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))) := inferInstance

example : (Sheaf.moduleLift (Λ := Λ) (Mod.forget R)
    (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))).ReflectsIsomorphisms := inferInstance

example : (Sheaf.moduleLift (Λ := Λ) (Mod.forget R)
    (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c))).Faithful := inferInstance

example : Sheaf.moduleLift (Λ := Λ) (Mod.forget R)
    (fun M ↦ (Mod.sectionActRingHom M).comp φ)
    (fun f c ↦ Mod.sectionActRingHom_comp_hom f (φ c)) ⋙
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) = Mod.forget R :=
  Sheaf.moduleLift_comp_sheafCompose (Λ := Λ) (Mod.forget R) _ _

end Example
