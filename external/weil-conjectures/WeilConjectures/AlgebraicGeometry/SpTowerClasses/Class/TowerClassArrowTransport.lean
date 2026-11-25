/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.UnderlyingSingleArrow

/-! # Underlying integral arrows with canonical abelian-tower endpoints -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Forget an integral arrow and use the canonical integer and root endpoints.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: def-sfb-tower-underlying-arrow).
This is the actual composite of the integer generator, exact forgetting and
rootForget. Its explicit endpoints share the abelian-tower category witnesses. -/
def underlyingChernArrow (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}}
    {R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    {φ : WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ R.obj (op n))
        (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ A.obj (op n))
        (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op)}
    (c : ChernData l T R A φ)
    (f : unit T R ⟶
      ((DerivedCategory.singleFunctor (Systems T R) 0).obj c.rootModule)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(2 : ℤ)⟧ :=
  underlyingSingleArrow (C := Systems T R) (D := Ab T) c.reduction.forget.F
    (integerGenerator T R c.reduction.forget) c.rootForget.hom f

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
