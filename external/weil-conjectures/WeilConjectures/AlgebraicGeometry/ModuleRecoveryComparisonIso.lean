/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Whiskering

/-! # Composition of the two comparisons in a module recovery equation

Source: the canonical comparison construction in
lem-pc-open-cover-map-lift-transport (Stacks Project, Tags 0095 and 0096).
-/

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- Combine a base-change composition comparison and a restriction comparison.
This is an explicit composite of supplied isomorphisms, with functor associators.
Source: the canonical comparison construction in lem-pc-open-cover-map-lift-transport.
(blueprint: def-pc-module-recovery-comparison-iso). -/
def moduleRecoveryComparisonIso
    {C E D K V : Type*}
    [Category* C] [Category* E] [Category* D] [Category* K] [Category* V]
    (T : C ⥤ D) (A : C ⥤ E) (B : E ⥤ D) (S : E ⥤ K) (P : K ⥤ V) (R : D ⥤ V)
    (e : T ≅ A ⋙ B) (t : S ⋙ P ≅ B ⋙ R) : T ⋙ R ≅ (A ⋙ S) ⋙ P :=
  Functor.isoWhiskerRight e R ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft A t.symm ≪≫ (Functor.associator _ _ _).symm

end AlgebraicGeometry
