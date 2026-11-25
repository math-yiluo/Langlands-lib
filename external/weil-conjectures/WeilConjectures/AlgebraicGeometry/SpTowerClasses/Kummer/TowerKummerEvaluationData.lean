/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerPositiveKummerBoundary

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

/-- The actual comparison formula, with its concrete endpoints shared by name.
Source: blueprint latest, geometric classes proof, clause (2).
(blueprint: def-sfb-kummer-boundary-evaluation-equality).
This predicate is exactly the stated equality of the actual Kummer arrows;
it adds no hypotheses and no existentially chosen data. -/
def KummerBoundaryEvaluationEquality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (k : Kummer l T)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) (n : ℕ) : Prop :=
  HEq (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
      (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ) (f ≫ towerKummerBoundary l k))
      (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
      (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ)
        (kummerComposite (C := Ab T) (ShortComplex.mk k.inclusion k.power k.zero) k.exact f))

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
