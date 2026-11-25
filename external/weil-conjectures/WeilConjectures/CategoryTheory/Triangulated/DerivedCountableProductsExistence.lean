/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Existence of countable products in the derived category under exact products.
Source: Stacks Project, Derived Categories, Lemma 13.34.2, Tag 07KC.
The construction takes termwise products of representative complexes and descends
through the derived localization; exactness of products makes products of
quasi-isomorphisms quasi-isomorphisms.
(blueprint: lem-weil-derived-countable-products-existence) -/
theorem derivedCategory_hasCountableProducts
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    HasCountableProducts (DerivedCategory A) := by
  classical
  refine ⟨fun J _ ↦ ⟨fun F ↦ ?_⟩⟩
  let C : J → CochainComplex A ℤ := fun j ↦ DerivedCategory.Q.objPreimage (F.obj ⟨j⟩)
  obtain ⟨h⟩ := derivedCategory_termwiseProduct_isLimit A J C
  have : HasLimit (Discrete.functor C ⋙ DerivedCategory.Q) :=
    HasLimit.mk ⟨DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C)), h⟩
  exact hasLimit_of_iso (Discrete.natIso
    (F := Discrete.functor C ⋙ DerivedCategory.Q) (G := F)
    fun j ↦ DerivedCategory.Q.objObjPreimageIso (F.obj j))

end CategoryTheory
