/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Restriction of scalars as a ringed-topos direct image

Source: Stacks, Modules on Sites, restriction of scalars and ringed topoi.
(blueprint: lem-weil-pbc-restriction-ringed-topos-module-direct-image).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private noncomputable def siteRestrictionRingedTopos
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : S ⟶ R) : RingedToposMorphism R S where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (forget RingCat.{u})).map c
  ring_zero := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 0
    rw [hz U t]
    exact (c.hom.app U).hom.map_zero
  ring_one := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 1
    rw [hz U t]
    exact (c.hom.app U).hom.map_one
  ring_add := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) + (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_add _ _
  ring_mul := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) * (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_mul _ _
  modules := SheafOfModules.restrictScalars c
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T a x y z hz U t
    exact hz U t
/-- Restriction along a ring-sheaf morphism is the direct image of its identity-site
ringed-topos morphism. Source: Stacks, Modules on Sites, Definition 01D3 and restriction
of scalars (blueprint: lem-weil-pbc-restriction-ringed-topos-module-direct-image).
Proof: take both set functors to be the identity and use the given ring map as the
structural map. Ring-homomorphism laws verify its four operations; restriction retains
the underlying additive sheaf, so the module identity is the given scalar-action law. -/
theorem restrictionRingedToposModuleDirectImage_exists
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : S ⟶ R) :
    ∃ r : RingedToposMorphism R S, r.modules = SheafOfModules.restrictScalars c :=
  ⟨siteRestrictionRingedTopos c, rfl⟩

end CategoryTheory
