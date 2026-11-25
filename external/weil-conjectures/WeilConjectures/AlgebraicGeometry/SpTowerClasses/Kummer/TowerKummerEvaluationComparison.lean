/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerEvaluationData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerBoundaryRawComparison

/-! # Evaluation of the named positive Kummer connecting arrow -/

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

/-- The named boundary evaluates to the existing finite Kummer composite.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-kummer-evaluation-comparison).
Proof: apply congrArg for exact evaluation to the proved equality between
composition with the named boundary and the original kummerComposite. No coefficient
tower or scalar-extension data are involved. Convert equality to HEq. -/
theorem towerKummerBoundary_evaluation (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) (n : ℕ) :
    KummerBoundaryEvaluationEquality l k f n := by
  exact (congrArg
    (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
      (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ))
    (towerKummerBoundary_eq_raw l k f)).heq

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
