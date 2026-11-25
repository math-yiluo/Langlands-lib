/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # A derived arrow presenting a strict degree-two Ext class -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Present an Ext class on specified derived endpoints, sharing all category data.
Source: the strict-class clause of the diagonal-limit characterization.
(blueprint: def-sfb-diagonal-trace-ext-arrow-presentation). -/
@[irreducible]
def ExtArrowPresentation
    {A : Type*} [Category A] [Abelian A] [HasExt A] [HasDerivedCategory A]
    {S H : A} (xi : Ext S H 2) {K J : DerivedCategory A}
    (a : K ≅ (DerivedCategory.singleFunctor A 0).obj S)
    (b : J ≅ ((DerivedCategory.singleFunctor A 0).obj H)⟦(2 : ℤ)⟧)
    (f : K ⟶ J) : Prop :=
  xi.hom = a.inv ≫ f ≫ b.hom

/-- Chosen derived endpoints and an arrow for a strict degree-two class.
All single, shift and derived-category structures are formed before specializing
objects to the concrete supported source.
Source: the strict-class clause of the diagonal-limit characterization.
(blueprint: def-sfb-diagonal-trace-ext-derived-presentation). -/
structure ExtDerivedPresentation
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (S H : A) where
  K : DerivedCategory A
  J : DerivedCategory A
  source : K ≅ (DerivedCategory.singleFunctor A 0).obj S
  target : J ≅ ((DerivedCategory.singleFunctor A 0).obj H)⟦(2 : ℤ)⟧
  arrow : K ⟶ J

/-- The specified arrow data presents the specified strict Ext class.
Source: the strict-class clause of the diagonal-limit characterization.
(blueprint: def-sfb-diagonal-trace-derived-presentation-equation). -/
@[irreducible]
def ExtDerivedPresentation.Presents
    {A : Type*} [Category A] [Abelian A] [HasExt A] [HasDerivedCategory A]
    {S H : A} (p : ExtDerivedPresentation S H) (xi : Ext S H 2) : Prop :=
  ExtArrowPresentation xi p.source p.target p.arrow

end AlgebraicGeometry.ProEtale.DiagonalTrace
