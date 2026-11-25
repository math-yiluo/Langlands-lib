/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ChernData.TowerChernTargetNormalizationData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex

/-! # The root-normalization equation in derived-arrow coordinates

Source: classes (2) (blueprint: lem-sp-tower-chern-root-normalization-equation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapHomologicalComplex
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  DerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime]

private def mkBoundary
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {U P V : C} (i : V ⟶ P) (p : P ⟶ U) (z : i ≫ p = 0)
    (hs : (ShortComplex.mk i p z).ShortExact) :
    (DerivedCategory.singleFunctor C 0).obj U ⟶
      ((DerivedCategory.singleFunctor C 0).obj V)⟦(1 : ℤ)⟧ := hs.singleδ

private theorem mk_target_equation
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (r : DerivedExtension L R) {U P V : C}
    (i : V ⟶ P) (p : P ⟶ U) (z : i ≫ p = 0)
    (hs : (ShortComplex.mk i p z).ShortExact) {Y : D}
    (e : r.derived.obj (((DerivedCategory.singleFunctor C 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj Y)⟦(2 : ℤ)⟧)
    (y : R.obj Y ≅ V) (h : r.targetNormalization (ShortComplex.mk i p z) hs e y) :
    (r.derivedAdjunction.homEquiv _ _) e.hom ≫
      (R.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor D 0).obj Y) ≫
      ((R.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor C 0).map y.hom)⟦(2 : ℤ)⟧' =
    (mkBoundary i p z hs)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor C 0).obj V) := by
  exact h

/-- The target normalization identifies the root transpose with the signed Kummer boundary.

Source: classes (2), normalization of integral reduction at the Kummer sequence
(blueprint: lem-sp-tower-chern-root-normalization-equation).

Proof: unfold the target-normalization predicate. Its four factors are the
adjunction transpose, shift comparison, single-complex comparison and root
identification. The right-hand side is exactly the positive short-exact boundary
shifted once, followed by the inverse shift-addition comparison. -/
theorem chern_root_normalization_equation
    (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    (h : c.rootNormalized l T R A φ) :
    (c.reduction.derivedAdjunction.homEquiv _ _) c.rootIso.hom ≫
      (c.reduction.forget.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Systems T R) 0).obj c.rootModule) ≫
      ((c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        c.rootModule)⟦(2 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor (Ab T) 0).map c.rootForget.hom)⟦(2 : ℤ)⟧' =
    c.kummer.boundary⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory (Ab T)) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T)) := by
  exact mk_target_equation c.reduction.model c.kummer.inclusion c.kummer.power
    c.kummer.zero c.kummer.exact c.rootIso c.rootForget h

end AlgebraicGeometry.ProEtale.SpTowerClasses
