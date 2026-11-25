/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Derived.DerivedPerfectSmallClassCoreAlpha

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- The well-generation and common cardinal-bound part of the perfect-class argument.

Source: Neeman, Theorem 0.2; Krause, Sections 6.2--6.3.
(blueprint: new-sfb-derived-perfect-small-class-core)

Proof: construct a sufficiently large regular cardinal above the well-generation bound and
above representatives for `P`; the alpha-compact objects form the required class. -/
theorem derived_exists_perfectSmallClass_core
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ (S : ObjectProperty (DerivedCategory A)) (α : Cardinal.{v})
      (_ : Fact α.IsRegular),
      ObjectProperty.EssentiallySmall.{v} S ∧ S.IsClosedUnderIsomorphisms ∧
      S.IsTriangulated ∧ P ≤ S ∧ (∀ (I : Type v) (Y : I → DerivedCategory A),
        HasCardinalLT I α → (∀ i, S (Y i)) → S (∐ Y)) ∧
      ∀ U, S U ↔ IsAlphaCompact U α := by
  obtain ⟨S, α, hα, hS, hSmall, hIso, hTri, hSum, hComp, hP⟩ :=
    derived_exists_alphaCompactClass_core P
  let _ : Fact α.IsRegular := hα
  refine ⟨S, α, hα, hSmall, hIso, hTri, ?_, hSum, hS⟩
  intro U hU
  exact (hS U).mpr (hP U hU)

end CategoryTheory
