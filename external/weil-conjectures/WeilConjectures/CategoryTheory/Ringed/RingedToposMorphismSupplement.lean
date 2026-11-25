/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.RingedToposMorphism

/-!
# Ringed-topos morphisms with their induced module direct images

Source: Stacks Project, Sites, Definition 00XA; Modules on Sites, morphisms of ringed
topoi and pushforward of modules (blueprint: def-weil-pbc-ringed-topos-morphism).

The structural map is written on inverse-image underlying sheaves. Ring operations and
module actions are specified using generalized elements. This avoids requiring a morphism
of the presented sites: arbitrary geometric morphisms of the sheaf topoi are allowed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [instance] RingedToposMorphism.additive

end CategoryTheory

-- Universe-general extension, N0 stage-2 repair; the original interface above is retained.
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe uC vC uD vD

namespace CategoryTheory


end CategoryTheory

namespace CategoryTheory

/-- A geometric morphism with a structural ring map and the induced direct image on modules.

Source: Stacks Project, Sites, Definition 00XA, and Modules on Sites, pushforward of modules
(blueprint: def-weil-pbc-ringed-topos-morphism).

The ring identities test every generalized element of the target topos. Left exactness
identifies the inverse image of products and the terminal object, so these are precisely
the identities for a morphism of ring objects. The last identity specifies addition and
scalar multiplication on the module direct image under the sheaf adjunction. It includes
zero by taking all three module elements zero. Thus the supplied module direct image is
the usual induced one, up to its displayed natural identification, not an arbitrary lift.
No exactness of the tensor module pullback or preservation of K-injectives is assumed. -/
structure RingedToposMorphismOnSites
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget RingCat.{u})]
    [K.HasSheafCompose (forget RingCat.{u})]
    [J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget AddCommGrpCat.{u})]
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type u) ⥤ Sheaf J (Type u)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type u) ⥤ Sheaf K (Type u)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (forget RingCat.{u})).obj B) ⟶
    (sheafCompose J (forget RingCat.{u})).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat.{u})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat.{u})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{u})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{u})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- The induced direct image on module sheaves. -/
  modules : ringedSiteModules.{u} A ⥤ ringedSiteModules.{u} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat.{u})) ⋙ direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : ringedSiteModules.{u} A) (T : Sheaf K (Type u))
    (a : T ⟶ (sheafCompose K (forget RingCat.{u})).obj B)
    (x y z : T ⟶ (sheafCompose K (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((inverse.map a) ≫ ringMap).hom.app U t)
            (((adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)

end CategoryTheory
