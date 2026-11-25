/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Isomorphisms of sheaves of modules from isomorphisms of the underlying abelian sheaves

Two sheaves of `R`-modules are isomorphic as soon as their underlying abelian sheaves are, by an
isomorphism commuting with the action of every `r : R` on sections
(`CategoryTheory.Sheaf.isoMkOfSheafCompose`), and likewise for functors to sheaves of
`R`-modules (`CategoryTheory.Sheaf.natIsoMkOfSheafCompose`).
-/

@[expose] public section

universe w v₁ u₁

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type w} [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]

/-- Two sheaves of `R`-modules are isomorphic as soon as their underlying abelian sheaves are,
by an isomorphism commuting with the action of every `r : R` on sections. -/
noncomputable def isoMkOfSheafCompose {G H : Sheaf J (ModuleCat.{w} R)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).obj G ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).obj H)
    (he : ∀ (U : Cᵒᵖ) (r : R) (y : G.obj.obj U), e.hom.hom.app U (r • y) =
      (fun z : H.obj.obj U ↦ r • z) (e.hom.hom.app U y)) :
    G ≅ H :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
      { (((sheafToPresheaf J Ab.{w}).mapIso e).app U).addCommGroupIsoToAddEquiv with
        map_smul' := he U })
      fun g ↦ by
        ext y
        exact ConcreteCategory.congr_hom (e.hom.hom.naturality g) y)

/-- Two functors to sheaves of `R`-modules are isomorphic as soon as the underlying abelian
sheaves of their values are, naturally, by isomorphisms commuting with the action of every
`r : R` on sections. -/
noncomputable def natIsoMkOfSheafCompose {D : Type*} [Category* D]
    {F₁ F₂ : D ⥤ Sheaf J (ModuleCat.{w} R)}
    (e : ∀ X : D, (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).obj (F₁.obj X) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).obj (F₂.obj X))
    (he : ∀ (X : D) (U : Cᵒᵖ) (r : R) (y : (F₁.obj X).obj.obj U),
      (e X).hom.hom.app U (r • y) =
        (fun z : (F₂.obj X).obj.obj U ↦ r • z) ((e X).hom.hom.app U y))
    (naturality : ∀ {X Y : D} (g : X ⟶ Y),
      (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).map (F₁.map g) ≫ (e Y).hom =
        (e X).hom ≫ (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).map (F₂.map g)) :
    F₁ ≅ F₂ :=
  NatIso.ofComponents (fun X ↦ isoMkOfSheafCompose (e X) (he X)) fun g ↦
    (sheafCompose J (forget₂ (ModuleCat.{w} R) Ab.{w})).map_injective (naturality g)

end CategoryTheory.Sheaf
