/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Lifting adjunctions to commutative group objects

An adjunction `F ⊣ G` between braided functors of cartesian monoidal categories lifts to an
adjunction `F.mapCommGrp ⊣ G.mapCommGrp` between the categories of commutative group objects
(`CategoryTheory.Adjunction.mapCommGrp`). This file records that the unit and counit of the
lifted adjunction have the unit and counit of `F ⊣ G` as underlying morphisms.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] [BraidedCategory C] [BraidedCategory D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) [F.Braided] [G.Braided]

/-- **An adjunction lifts to abelian group objects.** Let `F ⊣ G` be an adjunction between
cartesian monoidal categories whose functors are braided monoidal, e.g. product preserving
functors with the structure `Functor.Braided.ofChosenFiniteProducts`. Then `F` and `G` induce
functors `F.mapCommGrp`, `G.mapCommGrp` between the categories of commutative (abelian) group
objects, commuting with the forgetful functors, and `F.mapCommGrp ⊣ G.mapCommGrp`
(`Adjunction.mapCommGrp`) with unit and counit whose underlying morphisms are the unit and
counit of `F ⊣ G`; in particular these are morphisms of group objects.
(blueprint: `situation-conventions`) -/
theorem mapCommGrp_unit_counit :
    (∀ X : CommGrp C, (CommGrp.forget C).map (adj.mapCommGrp.unit.app X) = adj.unit.app X.X) ∧
    ∀ Y : CommGrp D, (CommGrp.forget D).map (adj.mapCommGrp.counit.app Y) =
      adj.counit.app Y.X :=
  ⟨fun _ ↦ (Category.id_comp _).trans (Category.comp_id _),
    fun _ ↦ (Category.id_comp _).trans (Category.comp_id _)⟩

end CategoryTheory.Adjunction
