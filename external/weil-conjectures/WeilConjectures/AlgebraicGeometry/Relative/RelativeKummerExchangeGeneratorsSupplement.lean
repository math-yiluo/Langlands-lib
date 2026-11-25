/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGenerators

/-!
# Exchange on normalized global generators

Global classes are derived morphisms out of the constant free rank-one module sheaf.
Sections are sheaf morphisms out of that same sheaf, equivalently their value on 1.
All comparisons below are the canonical single, constant, shift and adjunction comparisons.

## References

* Stacks Tags 0736 and 072W
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Generic
variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  (M : C)

end Generic

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStar lowerStar

private theorem adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

private theorem shifted_adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ) ℤ]
    {A : C} {K : D} (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map ((mateEquiv adj adj' θ).app K) =
      adj'.homEquiv (G.obj A) ((H.obj K)⟦q⟧)
        (θ.app A ≫ H.map z ≫ (H.commShiftIso q).hom.app K) ≫
          (R'.commShiftIso q).hom.app (H.obj K) := by
  have hs := NatTrans.shift_app_comm (mateEquiv adj adj' θ) q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [Functor.map_comp, Category.assoc, hs]
  rw [← Category.assoc, adjunct_mate]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right, Category.assoc]

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

end AlgebraicGeometry.Etale
