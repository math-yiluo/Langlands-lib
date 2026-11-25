/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Torsion sheaves and stalks

A sheaf of abelian groups `F` is torsion (`CategoryTheory.Sheaf.IsTorsion`) if every section
is locally torsion. This file shows that this is a stalkwise condition:

* the stalk `F_Φ` of a torsion sheaf at any point `Φ` of the site is a torsion group;
* conversely, if the stalks of `F` at the points of a conservative family are torsion groups,
  then `F` is torsion.

## Main results

- `CategoryTheory.GrothendieckTopology.Point.isAddTorsion_sheafFiber`: the stalks of a torsion
  sheaf are torsion groups.
- `CategoryTheory.Sheaf.IsTorsion.of_isAddTorsion_sheafFiber`: a sheaf whose stalks at a
  conservative family of points are torsion groups is torsion.
- `CategoryTheory.Sheaf.isTorsion_iff_isAddTorsion_sheafFiber`: the combination of the two.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable (Φ : J.Point.{w})

/-- The image of a section in the stalk is torsion as soon as the section is locally
torsion. -/
lemma isOfFinAddOrder_toPresheafFiber {F : Sheaf J AddCommGrpCat.{w}} {X : C}
    (x : Φ.fiber.obj X) (z : F.obj.obj (op X)) (S : Sieve X) (hS : S ∈ J X)
    (h : ∀ ⦃V : C⦄ ⦃f : V ⟶ X⦄, S f → IsOfFinAddOrder (F.obj.map f.op z)) :
    IsOfFinAddOrder (Φ.toPresheafFiber X x F.obj z) := by
  obtain ⟨Y, f, hf, y, rfl⟩ := Φ.jointly_surjective S hS x
  rw [← toPresheafFiber_w]
  exact (Φ.toPresheafFiber Y y F.obj).hom.isOfFinAddOrder (h hf)

variable [LocallySmall.{w} C]

/-- The stalks of a torsion sheaf of abelian groups are torsion groups. -/
lemma isAddTorsion_sheafFiber {F : Sheaf J AddCommGrpCat.{w}} (hF : F.IsTorsion) :
    IsAddTorsion ((Φ.sheafFiber (A := AddCommGrpCat.{w})).obj F) := by
  intro p
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) p
  obtain ⟨S, hS, h⟩ := hF z
  exact Φ.isOfFinAddOrder_toPresheafFiber x z S hS h

end GrothendieckTopology.Point

namespace Sheaf

variable [LocallySmall.{w} C]
  [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} [ObjectProperty.Small.{w} P]

/-- A sheaf of abelian groups whose stalks at the points of a conservative family are torsion
groups is torsion. -/
lemma IsTorsion.of_isAddTorsion_sheafFiber (hP : P.IsConservativeFamilyOfPoints)
    {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ Φ : P.FullSubcategory,
      IsAddTorsion ((Φ.obj.sheafFiber (A := AddCommGrpCat.{w})).obj F)) :
    F.IsTorsion := by
  intro U z
  let S : Sieve U.unop :=
    { arrows _ f := IsOfFinAddOrder (F.obj.map f.op z)
      downward_closed {_ _ f} hf g := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        exact (F.obj.map g.op).hom.isOfFinAddOrder hf }
  refine ⟨S, ?_, fun _ _ hf ↦ hf⟩
  obtain ⟨I, Y, f, hf⟩ := S.exists_eq_ofArrows
  rw [hf, hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  have hz : IsOfFinAddOrder (Φ.obj.toPresheafFiber _ x F.obj z) := hF Φ _
  obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hz
  rw [← map_nsmul, ← map_zero (Φ.obj.toPresheafFiber _ x F.obj).hom,
    GrothendieckTopology.Point.toPresheafFiber_eq_iff'] at h
  obtain ⟨V, g, y, rfl, hg⟩ := h
  have hgS : S g :=
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, by rwa [map_zero, map_nsmul] at hg⟩
  rw [hf] at hgS
  obtain ⟨W, a, b, ⟨i⟩, rfl⟩ := hgS
  exact ⟨i, Φ.obj.fiber.map a y, by simp⟩

/-- A sheaf of abelian groups is torsion if and only if its stalks at the points of a
conservative family are torsion groups. -/
lemma isTorsion_iff_isAddTorsion_sheafFiber (hP : P.IsConservativeFamilyOfPoints)
    (F : Sheaf J AddCommGrpCat.{w}) :
    F.IsTorsion ↔ ∀ Φ : P.FullSubcategory,
      IsAddTorsion ((Φ.obj.sheafFiber (A := AddCommGrpCat.{w})).obj F) :=
  ⟨fun hF Φ ↦ Φ.obj.isAddTorsion_sheafFiber hF, IsTorsion.of_isAddTorsion_sheafFiber hP⟩

end Sheaf

end CategoryTheory
