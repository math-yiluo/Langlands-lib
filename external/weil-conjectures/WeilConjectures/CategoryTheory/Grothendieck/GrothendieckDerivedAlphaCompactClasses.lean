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
public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedPerfectWellGenerators
import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactClassSmallClosed

/-! # The bounded alpha-compact subcategories of a Grothendieck derived category -/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Above a fixed rank, alpha-compact objects form an essentially small
extension-closed subcategory.

Source: Neeman, On the derived category of sheaves on a manifold, Theorem 0.2;
Krause (2001), Lemma 5, pages 124--125; Krause, Localization theory for
triangulated categories, Section 6.3.
(blueprint: new-sfb-derived-alpha-compact-classes)

Proof in words: choose the small shift-closed generating class G and its regular
smallness bound beta from derived_exists_perfect_well_generators. For every
regular alpha at least beta, monotonicity makes each object of G alpha-small.
Its (G4) and generation properties are independent of the cardinal. Apply
alphaCompactObjects_small_closed to obtain essential smallness and extension
closure of the canonical class at alpha. Thus beta works simultaneously for all
larger regular alpha. Repletion, zero, shifts, retracts and bounded coproducts
are separately proved by the alpha-compact API.
-/
theorem derived_alphaCompact_classes_eventually_small
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] :
    ∃ (β : Cardinal.{v}) (_ : Fact β.IsRegular),
      ∀ (α : Cardinal.{v}) [Fact α.IsRegular], β ≤ α →
        ObjectProperty.EssentiallySmall.{v} (alphaCompactObjects (DerivedCategory A) α) ∧
        (alphaCompactObjects (DerivedCategory A) α).IsTriangulatedClosed₂ := by
  obtain ⟨G, β, hβ, hGsmall, hGshift, hGsmallness, hGfactor, hGgen⟩ :=
    derived_exists_perfect_well_generators (A := A)
  let _ : ObjectProperty.EssentiallySmall.{v} G := hGsmall
  let _ : G.IsStableUnderShift ℤ := hGshift
  refine ⟨β, hβ, ?_⟩
  intro α hα hβα
  exact alphaCompactObjects_small_closed G α
    (fun X hX ↦ (hGsmallness X hX).of_le hβα) hGfactor hGgen

end CategoryTheory
