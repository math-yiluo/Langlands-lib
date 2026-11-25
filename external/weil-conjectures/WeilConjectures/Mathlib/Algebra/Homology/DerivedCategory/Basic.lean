/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The derived category of a zero category

If every object of an abelian category `C` is zero, so is every object of its derived category
(`DerivedCategory.isZero_of_forall_isZero`): every object is the image of a cochain complex,
and a cochain complex of zero objects is zero.

We also record that `DerivedCategory.Q` is the localization at the quasi-isomorphisms
(`DerivedCategory.isLocalization_Q`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If every object of `C` is zero, then every object of `D(C)` is zero. -/
lemma isZero_of_forall_isZero (h : ∀ X : C, IsZero X) (K : DerivedCategory C) : IsZero K := by
  have hK : IsZero (Q.objPreimage K) := by
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun n ↦ (h _).eq_of_src _ _
  exact (Q.map_isZero hK).of_iso (Q.objObjPreimageIso K).symm

/-- **The derived category is a localization.** For an abelian category `C`, the derived category
`D(C) = DerivedCategory C` is the localization of the category of cochain complexes
`CochainComplex C ℤ` at the quasi-isomorphisms (the morphisms inducing isomorphisms on all
cohomology objects), with localization functor `DerivedCategory.Q`; the universe of its
morphisms is fixed by `HasDerivedCategory.{w} C`.

(blueprint: `def-weil-abstract-derived-category`) -/
theorem isLocalization_Q :
    (Q (C := C)).IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstance


end DerivedCategory
