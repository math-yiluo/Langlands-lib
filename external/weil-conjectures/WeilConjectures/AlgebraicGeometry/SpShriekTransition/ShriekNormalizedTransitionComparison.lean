/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedCocycle
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedProperTransition
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedOpenTransition

/-! # Actual compact-support coefficient transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
  SemilinearSections.reduction SpTowerShriek.Fcomparison
  Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian scalarExtensionFunctor
variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The specified b followed by finite compact support of the input reduction.
The b in this definition is literally the proper counit mate followed by the open
scalar comparison, as fixed by reductionDirectImageComparison.
Source: blueprint paragraph (1), the displayed composite
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def word {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  letI := b.finite n
  letI := b.finite m
  (reductionDirectImageComparison (quotientMap l E h) c.i c.g).app
      ((SpTowerShriek.Ev l E X n).obj C) ≫
    (SpTowerShriek.finiteF l E b c m).map (rho l E b X h C)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The actual output reduction, conjugated by the canonical compact-support evaluations.
Source: blueprint paragraph (1); prose-09-23 evaluation identifications
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def actual {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  conjugateReduction (scalarExtensionFunctor (quotientMap l E h) Y)
    ((SpTowerShriek.Fcomparison l E b o c n).app C)
    ((SpTowerShriek.Fcomparison l E b o c m).app C)
    (rho l E b Y h ((SpTowerShriek.F l E b o c).obj C))

end AlgebraicGeometry.ProEtale.SpShriekTransition
