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
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Alpha-compactness supplies the perfectness and bounded-subcoproduct clauses.

Source: Krause, Localization theory, Sections 6.2--6.3 and Proposition 6.8.1.
(blueprint: new-sfb-derived-perfect-small-class-properties)

Proof: the canonical alpha-compact class satisfies Krause's (G4). Factor a map
into a coproduct through a coproduct of objects Z_i in that class. The componentwise
surjectivity hypothesis lifts each map Z_i to X_i, and their coproduct gives the
required lift. For the second clause alpha-smallness gives a support J of size
less than alpha; closure under such coproducts puts the supported coproduct in S. -/
theorem derived_perfectSmallClass_properties
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (S : ObjectProperty (DerivedCategory A)) (α : Cardinal.{v}) [Fact α.IsRegular]
    [ObjectProperty.EssentiallySmall.{v} S]
    [S.IsClosedUnderIsomorphisms] [S.IsTriangulated]
    (hSsum : ∀ (I : Type v) (Y : I → DerivedCategory A), HasCardinalLT I α →
      (∀ i, S (Y i)) → S (∐ Y))
    (hcompact : ∀ U, S U ↔ IsAlphaCompact U α) :
    (∀ (I : Type v) (X Y : I → DerivedCategory A) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) ∧
    (∀ (I : Type v) (Y : I → DerivedCategory A), (∀ i, S (Y i)) →
      ∀ (U : DerivedCategory A), S U → ∀ f : U ⟶ ∐ Y,
      ∃ (J : Type v) (a : J → I), S (∐ fun j ↦ Y (a j)) ∧
        ∃ g : U ⟶ ∐ fun j ↦ Y (a j),
          g ≫ Sigma.desc (fun j ↦ Sigma.ι Y (a j)) = f) := by
  have hfactor : S.IsCoproductFactorizationClass := by
    intro U hU I Y f
    obtain ⟨Z, hZ, a, g, hg⟩ := IsAlphaCompact.factorizationClass α U
      ((hcompact U).mp hU) I Y f
    exact ⟨Z, fun i ↦ (hcompact (Z i)).mpr (hZ i), a, g, hg⟩
  constructor
  · exact hfactor.perfect
  · intro I Y hY U hU f
    obtain ⟨J, hJ, g, hg⟩ := ((hcompact U).mp hU).isAlphaSmall I Y f
    exact ⟨J, Subtype.val, hSsum J (fun j : J ↦ Y j) hJ (fun j ↦ hY j), g, hg⟩

end CategoryTheory
