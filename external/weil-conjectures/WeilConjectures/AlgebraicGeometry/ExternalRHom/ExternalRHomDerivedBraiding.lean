/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Braiding compatibility of localization tensor constraints -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe w v u
set_option backward.isDefEq.respectTransparency false
theorem braided_ofIso
    {C D : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [Category D] [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) [F.LaxMonoidal] (e : F ≅ G)
    (h : ∀ X Y, (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X =
      Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom) (X Y : C) :
    letI := Functor.LaxMonoidal.ofIso e
    (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X =
      Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom := by
  change (β_ (G.obj X) (G.obj Y)).hom ≫
      (e.inv.app Y ⊗ₘ e.inv.app X) ≫ Functor.LaxMonoidal.μ F Y X ≫ e.hom.app (Y ⊗ X) =
    ((e.inv.app X ⊗ₘ e.inv.app Y) ≫
      Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y)) ≫ G.map (β_ X Y).hom
  rw [← BraidedCategory.braiding_naturality_assoc, reassoc_of% (h X Y)]
  simp only [Category.assoc]
  rw [e.hom.naturality]

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
attribute [local instance] DerivedCategory.hasColimitsOfSize_braidedCategory
attribute [local instance] DerivedCategory.braidedCategory'
