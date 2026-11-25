/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # Locally constant perfect complexes on the ordinary etale site

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.3.1;
Stacks Project, Tag 09BI (blueprint: def-per-etale-locally-constant-perfect-complex).

The perfect coefficient object is realized by the exact constant-sheaf functor.
Its derived functor is termwise constant sheaf on any representing complex.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Etale locally, the complex is the constant realization of a perfect coefficient
complex. The coefficient complex may depend on the member of the etale cover.
Perfectness is the recorded bounded finite-projective model predicate, with its
independent localization universe.
Source: Bhatt--Scholze, Definition 6.3.1; Stacks Project, Tag 09BI
(blueprint: def-per-etale-locally-constant-perfect-complex). -/
def IsLocallyConstantPerfectEtaleComplex (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (P : DerivedCategoryModule A S) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : 𝒰.I₀,
    ∃ M : _root_.DerivedCategory (ModuleCat.{u + 1} A),
      _root_.DerivedCategory.IsPerfectRingComplex M ∧
      Nonempty ((upperStar (ModuleCat.{u + 1} A) (𝒰.f i)).mapDerivedCategory.obj P ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology
          (ModuleCat.{u + 1} A)).mapDerivedCategory.obj M)

end AlgebraicGeometry.Etale
