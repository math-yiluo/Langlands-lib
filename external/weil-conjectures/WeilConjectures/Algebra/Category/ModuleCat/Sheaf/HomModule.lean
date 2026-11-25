/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Global sections acting on morphisms of sheaves of modules

Source: Stacks Project, Modules on Sites, Sections 03DD and 04TT
(blueprint: def-pur-sheaf-modules-hom-module).
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Cᵒᵖ ⥤ CommRingCat.{u})
  (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat.{u}))
  (M N : SheafOfModules.{v} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩)

/-- (blueprint: def-pur-sheaf-modules-hom-module) For a sheaf `R` of commutative rings,
global sections act on morphisms of sheaves of `R`-modules. At each object `U`, the
component of `s • φ` sends `x` to `s_U • φ_U x`. This equals both precomposition with
multiplication by `s` on `M` and postcomposition with multiplication by `s` on `N`;
composition is bilinear. Stacks Project, Modules on Sites, Sections 03DD and 04TT. -/
noncomputable instance homModule :
    Module (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat.{u})) (M ⟶ N) := by
  letI : Module (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat.{u}))
      (M.val ⟶ N.val) :=
    Module.compHom _ (PresheafOfModules.sectionsSMulHom N.val)
  let e : (M ⟶ N) ≃+ (M.val ⟶ N.val) :=
    { toFun := fun f => f.val
      invFun := fun f => ⟨f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact e.module _

/-- (blueprint: def-pur-sheaf-modules-hom-module) Composition of sheaf-module morphisms is
bilinear over the ring of global sections. Stacks Project, Modules on Sites, Section 04TT. -/
noncomputable instance homLinear :
    Linear (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat.{u}))
      (SheafOfModules.{v} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩) where
  homModule := homModule R hR
  smul_comp := by
    intro X Y Z s f g
    apply hom_ext
    change (f.val ≫ PresheafOfModules.sectionsSMul Y.val s) ≫ g.val =
      (f.val ≫ g.val) ≫ PresheafOfModules.sectionsSMul Z.val s
    rw [PresheafOfModules.sectionsSMul_naturality f.val s]
    rw [PresheafOfModules.sectionsSMul_naturality (f.val ≫ g.val) s]
    rw [Category.assoc]
  comp_smul := by
    intro X Y Z f s g
    apply hom_ext
    rfl

end SheafOfModules
