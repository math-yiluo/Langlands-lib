/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# Transport of free module objects along a monoidal functor

Let `F : C ⥤ D` be a (strong) monoidal functor and `R : C` a monoid object. Transporting the free
`R`-module `R ⊗ M` along `F` gives the free `F R`-module `F R ⊗ F M`: the structure isomorphism
`F (R ⊗ M) ≅ F R ⊗ F M` of `F` is `F R`-linear, naturally in `M`
(`CategoryTheory.Functor.mapModFreeFunctorIso`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

open scoped CategoryTheory.Obj

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R]

namespace Functor

/-- The structure morphism `F R ⊗ F M ⟶ F (R ⊗ M)` of a monoidal functor is `F R`-linear for the
free module structures. -/
lemma act_freeFunctor_comp_μ (M : C) :
    Mod.act ((Mod.freeFunctor (F.obj R)).obj (F.obj M)).X ≫ LaxMonoidal.μ F R M =
      F.obj R ◁ LaxMonoidal.μ F R M ≫ Mod.act ((F.mapMod R).obj ((Mod.freeFunctor R).obj M)).X := by
  change ((α_ (F.obj R) (F.obj R) (F.obj M)).inv ≫ (LaxMonoidal.μ F R R ≫ F.map MonObj.mul) ▷
      F.obj M) ≫ LaxMonoidal.μ F R M =
    F.obj R ◁ LaxMonoidal.μ F R M ≫ LaxMonoidal.μ F R (R ⊗ M) ≫
      F.map ((α_ R R M).inv ≫ MonObj.mul ▷ M)
  rw [F.map_comp, LaxMonoidal.associativity_inv_assoc, comp_whiskerRight, Category.assoc,
    Category.assoc, LaxMonoidal.μ_natural_left]

/-- `F (R ⊗ M) ≅ F R ⊗ F M` as `F R`-modules, naturally in `M`. -/
noncomputable def mapModFreeFunctorIso :
    Mod.freeFunctor R ⋙ F.mapMod R ≅ F ⋙ Mod.freeFunctor (F.obj R) :=
  NatIso.ofComponents
    (fun M ↦ (Mod.isoMk (M := (Mod.freeFunctor (F.obj R)).obj (F.obj M))
      (N := (F.mapMod R).obj ((Mod.freeFunctor R).obj M)) (Monoidal.μIso F R M)
      (act_freeFunctor_comp_μ F R M)).symm)
    (fun f ↦ Mod.hom_ext _ _ (by
      change F.map (R ◁ f) ≫ OplaxMonoidal.δ F R _ = OplaxMonoidal.δ F R _ ≫ F.obj R ◁ F.map f
      rw [OplaxMonoidal.δ_natural_right]))

@[reassoc (attr := simp)]
lemma mapModFreeFunctorIso_hom_app_hom (M : C) :
    ((F.mapModFreeFunctorIso R).hom.app M).hom = OplaxMonoidal.δ F R M :=
  rfl

@[reassoc (attr := simp)]
lemma mapModFreeFunctorIso_inv_app_hom (M : C) :
    ((F.mapModFreeFunctorIso R).inv.app M).hom = LaxMonoidal.μ F R M :=
  rfl

end Functor

end CategoryTheory
