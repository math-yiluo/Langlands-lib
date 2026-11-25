/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Classical module and derived predicates

Source: the Weil conjectures blueprint, `definition-classical-pro-etale-sheaves`
(blueprint: definition-classical-pro-etale-sheaves).

The predicates below use the canonical continuity maps on affine pro-étale
presentations, in the coefficient category used by the comparison adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A module sheaf is classical when its canonical continuity map is invertible on
every affine pro-étale presentation.
Source: current blueprint, `sk-def-pe-classical-definition/_section.md`
(blueprint: definition-classical-pro-etale-sheaves). -/
def IsClassicalModuleFor (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I),
    IsIso (continuityMap P F.obj)

/-- A derived pro-étale object is classical when all of its cohomology module sheaves
are classical.
Source: current blueprint, `sk-def-pe-classical-definition/_section.md`
(blueprint: definition-classical-pro-etale-sheaves). -/
def IsClassicalComplexFor (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ))) : Prop :=
  ∀ q : ℤ,
    IsClassicalModuleFor X Λ
      ((@DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) _ _
        (HasDerivedCategory.standard _) q).obj K)

/-- The full subcategory of bounded-below pro-étale complexes with classical cohomology.
Source: the blueprint definition of classical complexes and its bounded-below
derived-equivalence detail (blueprint: definition-classical-pro-etale-sheaves).
-/
def ClassicalPlus (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ObjectProperty (DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ IsClassicalComplexFor X Λ (DerivedCategory.Plus.ι.obj K)

end AlgebraicGeometry.ProEtale

end
