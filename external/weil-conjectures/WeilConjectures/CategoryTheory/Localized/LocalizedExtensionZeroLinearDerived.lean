/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

set_option linter.privateModule false

/-!
# Linearity of localized extension by zero on derived module sheaves

Source: Stacks Project, Modules on Sites, Tags 03CY, 03DI and 03DJ
(blueprint: lem-cbc-localized-extension-zero-linear-derived).
-/

@[expose] public section
set_option autoImplicit false
universe u a w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private abbrev underlyingRing {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D} (S : Sheaf K CommRingCat.{u + 1}) :=
  (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S

private def sectionScalar {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b)
    {M N : SheafOfModules.{u + 1} (underlyingRing S)}
    (b : B) (f : M ⟶ N) : M ⟶ N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ sigma V b • f.val.app V x
          map_add' := fun x y ↦ by rw [map_add, smul_add]
          map_smul' := fun t x ↦ by
            change sigma V b • f.val.app V (t • x) = t • (sigma V b • f.val.app V x)
            rw [(f.val.app V).hom.map_smul]
            change sigma V b • ((t : S.obj.obj V) • f.val.app V x) =
              (t : S.obj.obj V) • (sigma V b • f.val.app V x)
            rw [← mul_smul, ← mul_smul]
            congr 1
            exact mul_comm (sigma V b) (t : S.obj.obj V) }
      naturality := fun {V W} g ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change sigma W b • f.val.app W (M.val.map g x) =
          N.val.map g (sigma V b • f.val.app V x)
        rw [PresheafOfModules.naturality_apply, N.val.map_smul]
        change sigma W b • (show N.val.obj W from N.val.map g (f.val.app V x)) =
          S.obj.map g (sigma V b) • (show N.val.obj W from N.val.map g (f.val.app V x))
        rw [hsigma] }

@[instance_reducible] private def sectionModule {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b)
    (M N : SheafOfModules.{u + 1} (underlyingRing S)) :
    Module B (M ⟶ N) where
  smul := sectionScalar S B sigma hsigma
  one_smul f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V 1 • f.val.app V x = f.val.app V x
    rw [map_one, one_smul]
  mul_smul b b' f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V (b * b') • f.val.app V x =
      sigma V b • (sigma V b' • f.val.app V x)
    rw [map_mul, mul_smul]
  smul_zero b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V b • (0 : N.val.obj V) = 0
    exact smul_zero _
  smul_add b f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V b • (f.val.app V x + g.val.app V x) =
      sigma V b • f.val.app V x + sigma V b • g.val.app V x
    exact smul_add ..
  add_smul b b' f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V (b + b') • f.val.app V x =
      sigma V b • f.val.app V x + sigma V b' • f.val.app V x
    rw [map_add, add_smul]
  zero_smul f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change sigma V 0 • f.val.app V x = 0
    rw [map_zero, zero_smul]

@[instance_reducible] private def sectionLinear {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D}
    (S : Sheaf K CommRingCat.{u + 1}) (B : Type a) [CommRing B]
    (sigma : ∀ V : Dᵒᵖ, B →+* S.obj.obj V)
    (hsigma : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) (b : B),
      S.obj.map f (sigma V b) = sigma W b) :
    Linear B (SheafOfModules.{u + 1} (underlyingRing S)) where
  homModule := sectionModule S B sigma hsigma
  smul_comp M N P b f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change g.val.app V (sigma V b • f.val.app V x) =
      sigma V b • g.val.app V (f.val.app V x)
    exact (g.val.app V).hom.map_smul _ _
  comp_smul M N P f b g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u + 1})
  (A : Type a) [CommRing A]
  (U : C)
  (rho : ∀ V : Cᵒᵖ, A →+* O.obj.obj V)
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u + 1}
    (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U))]
end CategoryTheory
