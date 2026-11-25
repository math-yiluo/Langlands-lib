/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Pointwise left Kan extensions along functors between large categories

For categories `C` and `D` with objects in `Type (u + 1)` and `Hom`-types in `Type u`, every
functor `F : C ⥤ D` admits pointwise left Kan extensions of all functors `C ⥤ A` to a
category `A` with colimits of size `u + 1`
(`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize`).
This applies in particular to the opposites of functors between the small sites of a scheme.
-/

@[expose] public section

universe u' u

namespace CategoryTheory.Functor

open Limits

/-- For categories `C` and `D` with objects in `Type (u + 1)` and `Hom`-types in `Type u`,
every functor `C ⥤ A` has a pointwise left Kan extension along every functor `F : C ⥤ D`,
provided `A` has colimits of size `u + 1`. -/
instance hasPointwiseLeftKanExtension_of_hasColimitsOfSize {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D) {A : Type u'} [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] (G : C ⥤ A) :
    F.HasPointwiseLeftKanExtension G := by
  intro V
  -- the indexing comma category has objects in `Type (u + 1)` and `Hom`-types in `Type u`
  have : HasColimitsOfShape (CostructuredArrow F V) A :=
    hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _
  infer_instance

end CategoryTheory.Functor
