/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassArrowTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerPositiveKummerBoundary

/-! # The integral boundary comparison for variable Chern coefficient towers -/

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

/-- The exact integral boundary equality, with its category witnesses shared by name.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: def-sfb-integral-boundary-normalization).
Fact wraps the actual equality of the transported integral arrow and the positive
Kummer composite, including its prescribed shift-addition comparison. -/
def IntegralBoundaryNormalization (l : ℕ) [Fact l.Prime]
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
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) : Prop :=
  Fact <|
    @Eq ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(2 : ℤ)⟧)
      (underlyingChernArrow l c
        (c.unitIso.inv ≫ c.reduction.model.derived.map f ≫ c.rootIso.hom))
      (f ≫ towerKummerBoundary l c.kummer)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
