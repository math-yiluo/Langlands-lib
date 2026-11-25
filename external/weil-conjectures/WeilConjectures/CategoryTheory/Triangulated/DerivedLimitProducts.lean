/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties

@[expose] public section
universe t w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Exact countable products descend to the derived category and commute with homology.
Source: Stacks Project, Derived Categories, Lemma 13.34.2, Tag 07KC
(blueprint: lem-weil-derived-limit-products-core).

Proof: Exact products preserve the short exact sequences defining cycles, boundaries and
homology, so homology commutes with termwise products and products of quasi-isomorphisms
are quasi-isomorphisms. Maps and homotopies into a termwise product are component families.
In the homotopy-category localization, represent each map into a factor by a left fraction
with denominator out of that factor. Taking the product of the denominators gives a
quasi-isomorphism and assembles these fractions into a map to the product. For uniqueness,
represent a map to the product by a fraction. If its projections vanish, refine the
component fractions until their composites are zero up to homotopy and their denominator
squares commute up to homotopy. Taking products of the refinements and the homotopies
makes the original fraction zero. Subtract two candidate lifts to obtain uniqueness.
Thus the image of each termwise product cone is limiting. Essential surjectivity of Q
supplies representatives of every countable diagram, proving existence of products.
The homology identifications from the first step respect all projections and so show
preservation of each countable discrete limit, including the empty product. -/
theorem derivedCategory_countableProducts_core
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    ∃ hP : HasCountableProducts (DerivedCategory A),
      letI : HasCountableProducts (DerivedCategory A) := hP
      (∀ (J : Type t) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      (∀ (J : Type t) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A p)) := by
  let hP : HasCountableProducts (DerivedCategory A) :=
    derivedCategory_hasCountableProducts A
  have hprops := @derivedCategory_countableProducts_properties A _ _ _ _ _ hP
  exact ⟨hP, hprops⟩

end CategoryTheory
