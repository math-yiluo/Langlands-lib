/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerCanonicalKummerExact
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PositiveExactBoundary

/-! # The positive Kummer connecting arrow with canonical endpoints -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The positive connecting morphism, shifted once and followed by shift addition.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: def-sfb-positive-kummer-boundary).
This is the actual connecting morphism of the given short exact Kummer sequence,
with explicitly named abelian-tower endpoints. -/
def towerKummerBoundary (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (k : Kummer l T) :
    ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(2 : ℤ)⟧ :=
  positiveExactBoundary (C := Ab T)
    (towerKummerComplex l k) (towerKummerShortExact l k)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
