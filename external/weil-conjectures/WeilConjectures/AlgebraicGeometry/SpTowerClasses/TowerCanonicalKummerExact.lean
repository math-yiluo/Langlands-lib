/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerCanonicalKummerComplex

/-! # Exactness of the concrete named Kummer complex -/

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

/-- The named actual Kummer complex is short exact.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-canonical-kummer-exact).
Proof: the named complex has exactly the objects and maps of the complex in the
exact field of k. The zero-morphism presentations are definitionally equal, and
the zero-composite proofs are proof irrelevant. Thus k.exact proves the assertion.
This adds no condition on k, the scheme, or the coefficient prime. -/
theorem towerKummerShortExact (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (k : Kummer l T) :
    (towerKummerComplex l k).ShortExact := by
  exact k.exact

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
