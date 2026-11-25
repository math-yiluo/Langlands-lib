/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import all Mathlib.Algebra.Homology.Localization

/-!
# Counit normalization for a derived functor representative

Source: Stacks Project, sites-cohomology.tex, Tag 07A4; the native exact-derived
comparison counit equation in `LeftDerivedFunctor.MapDerivedCategoryCounit`.

The factor comparison of an exact left-derived functor is its canonical counit on
the quotient of a cochain complex.
(blueprint: lem-sf-finite-open-mixed-tensor-representative-leftDerivedFactors-eq-counit)

Proof. Apply the defining comparison equation at the homotopy quotient of the
complex. Unfold the quotient comparison and the homotopy-category factor maps;
the identity maps cancel, leaving exactly the displayed counit.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- On a quotient complex the canonical exact-derived factors compose to the counit.

Proof. Evaluate the published homotopy factorization at the quotient complex, expand
the cochain-to-homotopy comparison factors, and cancel their identity components.
Source: Stacks Project, Tag 07A4; the native exact-derived counit factorization.
(blueprint: lem-sf-finite-open-mixed-tensor-representative-leftDerivedFactors-eq-counit) -/
theorem leftDerivedFactors_eq_counit
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (L : C ⥤ D) [L.Additive] [Limits.PreservesFiniteLimits L]
    [Limits.PreservesFiniteColimits L]
    (Z : CochainComplex C ℤ) :
    L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Z) ≫
        L.mapDerivedCategoryFactors.hom.app Z =
      cast (by rfl) (L.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj Z)) := by
  have h := L.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    ((HomotopyCategory.quotient _ _).obj Z)
  rw [CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app] at h
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  rw [cast_eq]
  exact h

end CategoryTheory.Functor
