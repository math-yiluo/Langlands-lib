/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerBoundaryRawData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerCompositeComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerRawComparison

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

/-- The named positive Kummer boundary gives the existing raw composite.
Source: blueprint latest, geometric classes proof, clause (2).
(blueprint: lem-sfb-kummer-boundary-raw-comparison).
Proof: compose the proved equality with the named-complex composite and
the proved proof-irrelevance comparison to the original literal complex. -/
theorem towerKummerBoundary_eq_raw (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) :
    KummerBoundaryRawEquality l k f := by
  exact (towerKummerBoundary_composite l k f).trans (towerKummerComposite_eq_raw l k f)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
