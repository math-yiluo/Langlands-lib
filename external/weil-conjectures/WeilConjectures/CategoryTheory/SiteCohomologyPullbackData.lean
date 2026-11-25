/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Families and normalization for pullback on object cohomology

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB.
(blueprint: lem-weil-pbc-site-cohomology-pullback-data)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

namespace Sheaf

/-- Evaluate a degree-zero object-cohomology class on the universal generator. -/
noncomputable abbrev objectCohomologyEval₀ {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] (x : Sheaf.H' A 0 V) : A.obj.obj (op V) :=
  ((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V)))

/-- Evaluation on the universal generator is natural in the coefficient sheaf. -/
theorem objectCohomologyEval₀_naturality {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) {A B : Sheaf J AddCommGrpCat.{u}}
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] (f : A ⟶ B) (x : Sheaf.H' A 0 V) :
    objectCohomologyEval₀ J V B
      ((((cohomologyPresheafFunctor J 0).map f).app (op V)).hom x) =
      (f.hom.app (op V)).hom (objectCohomologyEval₀ J V A x) := by
  change objectCohomologyEval₀ J V B
    (Abelian.Ext.comp x (Abelian.Ext.mk₀ f) (add_zero 0)) = _
  have h : Abelian.Ext.addEquiv₀ (x.comp (Abelian.Ext.mk₀ f) (add_zero 0)) =
      Abelian.Ext.addEquiv₀ x ≫ f := by
    apply (Abelian.Ext.mk₀_bijective _ B).injective
    rw [Abelian.Ext.mk₀_addEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_addEquiv₀_apply]
  simp only [objectCohomologyEval₀, h]
  rfl

/-- A morphism from the free abelian sheaf on an object is determined by its generator. -/
theorem objectCohomologyEval₀_injective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] :
    Function.Injective (objectCohomologyEval₀ J V A) := by
  intro x y h
  apply Abelian.Ext.addEquiv₀.injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ A.property
  ext X a
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | neg a ha => simp only [map_neg, ha]
  | add a b ha hb => simp only [map_add, ha, hb]
  | of f =>
    have hx := congrArg (fun t ↦ (A.obj.map f.op).hom t) h
    have hn (z : Sheaf.H' A 0 V) :
        ((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free) ≫
          (Abelian.Ext.addEquiv₀ z).hom).app X).hom (FreeAbelianGroup.of f) =
          (A.obj.map f.op).hom (objectCohomologyEval₀ J V A z) := by
      have ht := (toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free) ≫
        (Abelian.Ext.addEquiv₀ z).hom).naturality f.op
      have he := congrArg (fun q ↦ q.hom (FreeAbelianGroup.of (𝟙 V))) ht
      simpa [objectCohomologyEval₀] using he
    exact (hn x).trans (hx.trans (hn y).symm)

end Sheaf

/-- A family of maps on cohomology over objects, with the inverse image fixed. -/
abbrev SiteCohomologyFamily {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf K AddCommGrpCat.{u})] :=
  ∀ (p : ℕ) (V : C) (A : Sheaf J AddCommGrpCat.{u}),
    Sheaf.H' A p V ⟶ Sheaf.H' ((sheafPullback U AddCommGrpCat.{u} J K).obj A) p (U.obj V)

namespace SiteCohomologyFamily

/-- Naturality, compatibility with the Yoneda connecting map, and unit normalization. -/
abbrev IsPullback {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] [(sheafPullback U AddCommGrpCat.{u} J K).Additive]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    (fstar : SiteCohomologyFamily J K U) : Prop :=
  (∀ (p : ℕ) (V : C) (A A' : Sheaf J AddCommGrpCat.{u}) (φ : A ⟶ A'),
    ((Sheaf.cohomologyPresheafFunctor J p).map φ).app (op V) ≫ fstar p V A' =
      fstar p V A ≫ ((Sheaf.cohomologyPresheafFunctor K p).map
        ((sheafPullback U AddCommGrpCat.{u} J K).map φ)).app (op (U.obj V))) ∧
  (∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{u})) (hS : S.ShortExact)
    (hS' : (S.map (sheafPullback U AddCommGrpCat.{u} J K)).ShortExact)
    (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
    (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
      Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
  (∀ (V : C) (A : Sheaf J AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
    Sheaf.objectCohomologyEval₀ K (U.obj V) _ ((fstar 0 V A).hom x) =
      (((sheafAdjunctionContinuous U AddCommGrpCat.{u} J K).unit.app A).hom.app (op V)).hom
        (Sheaf.objectCohomologyEval₀ J V A x))

end SiteCohomologyFamily
end CategoryTheory
