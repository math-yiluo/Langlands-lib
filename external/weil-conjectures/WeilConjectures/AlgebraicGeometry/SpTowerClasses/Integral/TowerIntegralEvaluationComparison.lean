/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralBoundaryData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import Mathlib.Basic.Logic.Lemmas

/-! # Exact evaluation of the integral normalization -/

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

/-- Exact finite evaluation preserves the normalized integral boundary equality.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-integral-evaluation-comparison).
Proof: project the integral equality from Fact and apply congr_arg_heq to
mapSingleArrow for exact evaluation, keeping both coefficient towers variable.
This gives the required heterogeneous equality directly. -/
theorem integralEvaluation_of_normalization (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}}
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ R.obj (op n))
        (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ A.obj (op n))
        (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) (n : ℕ)
    (hi : IntegralBoundaryNormalization l R A φ c f) :
    HEq (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
        (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ)
      (underlyingChernArrow l c
        (c.unitIso.inv ≫ c.reduction.model.derived.map f ≫ c.rootIso.hom)))
      (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
        (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ)
        (f ≫ towerKummerBoundary l c.kummer)) := by
  exact congr_arg_heq
    (mapSingleArrow (C := Ab T) (D := DiagonalAb T)
      (X := integers T) (Y := roots l T) (abEvaluation T n) (2 : ℤ)) hi.out

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
