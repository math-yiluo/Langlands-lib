/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerPositiveKummerBoundary

/-! # The named positive Kummer boundary in the original coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The actual comparison formula, with its concrete endpoints shared by name.
Source: blueprint latest, geometric classes proof, clause (2).
(blueprint: def-sfb-kummer-boundary-raw-equality).
This predicate is exactly the stated equality of the actual Kummer arrows;
it adds no hypotheses and no existentially chosen data. -/
def KummerBoundaryRawEquality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) : Prop :=
  f ≫ towerKummerBoundary l k =
      kummerComposite (C := Ab T)
        (ShortComplex.mk k.inclusion k.power k.zero) k.exact f

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
