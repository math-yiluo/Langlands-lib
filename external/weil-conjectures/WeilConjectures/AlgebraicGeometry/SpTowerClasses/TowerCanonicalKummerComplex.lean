/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems

/-! # The actual Kummer complex with a shared zero witness -/

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
attribute [local instance 2000] Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

/-- The actual Kummer complex, with the canonical abelian-category zero witness.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: def-sfb-canonical-kummer-complex).
The objects, inclusion, power map and zero-composite proof are the fields of k;
only the definitionally equal zero-instance presentation is shared by name. -/
def towerKummerComplex (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (k : Kummer l T) :
    ShortComplex (Ab T) :=
  ShortComplex.mk (X₁ := roots l T) (X₂ := powerUnits l T) (X₃ := units T)
    k.inclusion k.power k.zero

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
