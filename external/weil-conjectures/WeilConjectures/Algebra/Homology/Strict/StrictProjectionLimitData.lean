/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.Functor

/-!
# Strict derived-limit data and diagram postcomposition

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941
(blueprint: def-sbc-strict-projection-tower-data).

The total right derived limit, K-injective computation, evaluation and natural Roos data
are the supplied data of lem-weil-pbc-ringed-strict-tower-homotopy-limit for module sheaves.
This record does not assert existence in an arbitrary abelian category.
`projectionPost` is Mathlib's ordinary diagram postcomposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uI vI uB vB uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace SheafOfModules

/-- Postcomposition on diagrams, retaining the original functor and natural transformations.
Source: Stacks 0940 (blueprint: def-sbc-strict-projection-tower-data). -/
abbrev projectionPost {I : Type uI} {B : Type uB} {D : Type uD}
    [Category.{vI} I] [Category.{vB} B] [Category.{vD} D] (F : B ⥤ D) :=
  (Functor.whiskeringRight I B D).obj F

/-- The derived limit, evaluation, and Roos data for an abelian category of strict towers.
For sheaves of modules these are the data supplied by
`ringedStrictTowerHomotopyLimitIndependentCoefficients`
(lem-weil-pbc-ringed-strict-tower-homotopy-limit). This record only packages supplied data.
Source: Stacks 0A07, 0940, 0941
(blueprint: def-sbc-strict-projection-tower-data). -/
structure StrictProjectionLimitData (B : Type uB) [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasCountableProducts DB]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))] where
  L : DT ⥤ DB
  eta : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ Q ⟶ QT ⋙ L
  ev : DT ⥤ (ℕᵒᵖ ⥤ DB)
  evaluation : QT ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (eta.app I)
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

end SheafOfModules
