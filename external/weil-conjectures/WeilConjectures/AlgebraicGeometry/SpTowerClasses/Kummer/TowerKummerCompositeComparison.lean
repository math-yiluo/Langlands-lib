/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerPositiveKummerBoundary

/-! # The named positive Kummer composite -/

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

/-- The named positive boundary gives exactly the original Kummer composite.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-kummer-composite-comparison).
Proof: both expressions compose f with the connecting morphism of k.exact shifted
once and the same inverse shift-addition isomorphism. Unfolding the two names
therefore proves equality by reflexivity. -/
theorem towerKummerBoundary_composite (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) :
    f ≫ towerKummerBoundary l k =
      kummerComposite (C := Ab T) (towerKummerComplex l k) (towerKummerShortExact l k) f := by
  unfold towerKummerBoundary positiveExactBoundary kummerComposite
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
