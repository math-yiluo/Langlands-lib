/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.CoinduceZMod

/-!
# Abelian sheaves killed by `n` as sheaves of `ℤ/n`-modules

An abelian group killed by a natural number `n` is canonically a `ℤ/n`-module, and every
morphism of abelian groups between `ℤ/n`-modules is `ℤ/n`-linear. Consequently, an abelian
sheaf killed by `n` is canonically a sheaf of `ℤ/n`-modules. In this file, we do this
functorially: a functor `P : 𝒜 ⥤ Sheaf J AddCommGrpCat` such that each `P.obj a` is killed
by `n` lifts along the forgetful functor
`sheafCompose J (forget₂ (ModuleCat (ULift (ZMod n))) AddCommGrpCat)`.

## Main definitions and results

- `CategoryTheory.Sheaf.zmodModuleLift n P hP : 𝒜 ⥤ Sheaf J (ModuleCat (ULift (ZMod n)))`: the
  lift of `P`.
- `CategoryTheory.Sheaf.zmodModuleLiftCompIso n P hP`: the composition of the lift with the
  forgetful functor is `P` (the components are identities).
- The lift preserves finite limits, finite colimits, or is additive, as soon as `P` does. For
  finite colimits, we use that the forgetful functor on sheaves is a left adjoint, because
  `forget₂` is (its right adjoint being coinduction `coindZMod`).
- `CategoryTheory.Sheaf.isIso_zmodModuleLift_map_iff`: the lift maps a morphism to an isomorphism
  if and only if `P` does.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AddCommGroup

/-- The `ULift (ZMod n)`-module structure on an abelian group killed by `n`. -/
noncomputable abbrev uliftZModModule (n : ℕ) {G : Type*} [AddCommGroup G]
    (h : ∀ x : G, n • x = 0) : Module (ULift.{w} (ZMod n)) G :=
  letI := AddCommGroup.zmodModule h
  Module.compHom G (ULift.ringEquiv : ULift.{w} (ZMod n) ≃+* ZMod n).toRingHom

end AddCommGroup

namespace AddCommGrpCat

variable (n : ℕ)

/-- An abelian group killed by `n`, as a `ULift (ZMod n)`-module. -/
noncomputable def toZModModuleCat (M : AddCommGrpCat.{w}) (hM : ∀ x : M, n • x = 0) :
    ModuleCat.{w} (ULift.{w} (ZMod n)) :=
  letI := AddCommGroup.uliftZModModule.{w} n hM
  ModuleCat.of _ M

/-- A morphism between abelian groups killed by `n`, as a `ULift (ZMod n)`-linear map. -/
noncomputable def toZModModuleCatHom {M N : AddCommGrpCat.{w}} (hM : ∀ x : M, n • x = 0)
    (hN : ∀ x : N, n • x = 0) (f : M ⟶ N) :
    toZModModuleCat n M hM ⟶ toZModModuleCat n N hN :=
  letI := AddCommGroup.zmodModule hM
  letI := AddCommGroup.zmodModule hN
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := fun c x ↦ ZMod.map_smul f.hom c.down x }

end AddCommGrpCat

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- If `m • 𝟙 F = 0` for an abelian sheaf `F`, then every section of `F` is killed by `m`. -/
lemma zsmul_apply_eq_zero {F : Sheaf J AddCommGrpCat.{w}} {m : ℤ} (h : m • 𝟙 F = 0)
    (U : Cᵒᵖ)
    (x : F.obj.obj U) : m • x = 0 := by
  have := congr_arg
    (fun f : F ⟶ F ↦ (sheafToPresheaf J _ ⋙ (evaluation _ _).obj U).map f x) h
  simpa only [Functor.map_zsmul, Functor.map_id, Functor.map_zero, AddCommGrpCat.hom_zsmul,
    AddCommGrpCat.hom_id, AddCommGrpCat.hom_zero, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply,
    AddMonoidHom.zero_apply] using this

/-- If `(n : ℤ) • 𝟙 F = 0` for an abelian sheaf `F`, then every section of `F` is killed by
`n`. -/
lemma nsmul_apply_eq_zero {F : Sheaf J AddCommGrpCat.{w}} {n : ℕ} (h : (n : ℤ) • 𝟙 F = 0)
    (U : Cᵒᵖ) (x : F.obj.obj U) : n • x = 0 := by
  rw [← natCast_zsmul]
  exact zsmul_apply_eq_zero h U x

variable {𝒜 : Type*} [Category* 𝒜] (n : ℕ) (P : 𝒜 ⥤ Sheaf J AddCommGrpCat.{w})
  (hP : ∀ a, (n : ℤ) • 𝟙 (P.obj a) = 0)

/-- The presheaf of `ULift (ZMod n)`-modules underlying `zmodModuleLift`. -/
noncomputable def zmodModuleLiftPresheaf (a : 𝒜) :
    Cᵒᵖ ⥤ ModuleCat.{w} (ULift.{w} (ZMod n)) where
  obj U := AddCommGrpCat.toZModModuleCat n _ (nsmul_apply_eq_zero (hP a) U)
  map f := AddCommGrpCat.toZModModuleCatHom n _ _ ((P.obj a).obj.map f)
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom ((P.obj a).obj.map_id U) x
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom ((P.obj a).obj.map_comp f g) x

/-- A functor `P : 𝒜 ⥤ Sheaf J AddCommGrpCat` with values killed by `n` lifts to sheaves of
`ULift (ZMod n)`-modules. -/
noncomputable def zmodModuleLift : 𝒜 ⥤ Sheaf J (ModuleCat.{w} (ULift.{w} (ZMod n))) where
  obj a := ⟨zmodModuleLiftPresheaf n P hP a,
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ _ AddCommGrpCat.{w}) (P.obj a).property⟩
  map f :=
    { hom :=
        { app U := AddCommGrpCat.toZModModuleCatHom n _ _ ((P.map f).hom.app U)
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

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})]

/-- The lift `zmodModuleLift n P hP` composed with the forgetful functor is `P`. -/
noncomputable def zmodModuleLiftCompIso :
    zmodModuleLift n P hP ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w}) ≅ P :=
  Iso.refl _

/-- `zmodModuleLift n P hP` maps a morphism to an isomorphism if and only if `P` does. -/
lemma isIso_zmodModuleLift_map_iff {a b : 𝒜} (f : a ⟶ b) :
    IsIso ((zmodModuleLift n P hP).map f) ↔ IsIso (P.map f) :=
  ⟨fun _ ↦ inferInstanceAs
      (IsIso ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
        ((zmodModuleLift n P hP).map f))),
    fun _ ↦ by
      have : IsIso ((sheafCompose J (forget₂ _ AddCommGrpCat.{w})).map
          ((zmodModuleLift n P hP).map f)) := inferInstanceAs (IsIso (P.map f))
      exact isIso_of_reflects_iso _ (sheafCompose J (forget₂ _ AddCommGrpCat.{w}))⟩

instance [P.ReflectsIsomorphisms] : (zmodModuleLift n P hP).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso (P.map f) := (isIso_zmodModuleLift_map_iff n P hP f).1 inferInstance
    exact isIso_of_reflects_iso f P

instance [P.Faithful] : (zmodModuleLift n P hP).Faithful :=
  Functor.Faithful.of_comp_iso (zmodModuleLiftCompIso n P hP)

instance [Preadditive 𝒜] [P.Additive] : (zmodModuleLift n P hP).Additive where
  map_add {a b f g} := by
    ext U x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congr_arg (fun f : P.obj a ⟶ P.obj b ↦ f.hom)
        (P.map_add (f := f) (g := g))) U) x

/-- The forgetful functor from sheaves of `ULift (ZMod n)`-modules to abelian sheaves preserves
finite limits. -/
instance preservesFiniteLimits_sheafCompose_forget₂_zmod :
    PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w}) ⋙
        sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) _)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance [PreservesFiniteLimits P] : PreservesFiniteLimits (zmodModuleLift n P hP) := by
  have : PreservesFiniteLimits
      (zmodModuleLift n P hP ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w})) :=
    inferInstanceAs (PreservesFiniteLimits P)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafCompose J (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w}))

/-- The forgetful functor from sheaves of `ULift (ZMod n)`-modules to abelian sheaves is a left
adjoint, since `forget₂` is a left adjoint and commutes with sheafification. -/
instance isLeftAdjoint_sheafCompose_forget₂_zmod [HasWeakSheafify J AddCommGrpCat.{w}] :
    (sheafCompose J
      (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})).IsLeftAdjoint := by
  have : (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w}).IsLeftAdjoint :=
    (forget₂CoindZModAdj n).isLeftAdjoint
  have : (coindZMod.{w} n).IsRightAdjoint := (forget₂CoindZModAdj n).isRightAdjoint
  exact Functor.isLeftAdjoint_of_iso
    (Functor.isoWhiskerLeft (sheafCompose J (forget₂ _ AddCommGrpCat.{w}))
      (sheafificationNatIso J AddCommGrpCat.{w}).symm ≪≫
      Functor.rightUnitor _ :
      Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) _) ≅ _)

instance [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify J (ModuleCat.{w} (ULift.{w} (ZMod n)))] [PreservesFiniteColimits P] :
    PreservesFiniteColimits (zmodModuleLift n P hP) := by
  have : PreservesFiniteColimits
      (zmodModuleLift n P hP ⋙ sheafCompose J (forget₂ _ AddCommGrpCat.{w})) :=
    inferInstanceAs (PreservesFiniteColimits P)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (sheafCompose J (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w}))

end Sheaf

end CategoryTheory
