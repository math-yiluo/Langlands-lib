/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The canonical symmetry of the etale derived tensor product

Source: Stacks Project, Tag 06YU, symmetry of the derived tensor product
(blueprint: lem-kun-tensor-sym).

The recorded existence theorem forgets the canonical map. This interface exposes the actual
braiding descended from the signed braiding of cochain complexes, without choosing an arbitrary
isomorphism from that existence theorem.

## Main definitions

- `CategoryTheory.DerivedMonoidal.canonicalBraidingNatIso`: the natural braiding before
  specializing to etale sheaves.
- `AlgebraicGeometry.Etale.derivedTensorSymmetry`: its canonical etale specialization.
-/

@[expose] public section

universe v₁ v₂ u' u

open CategoryTheory Limits

namespace CategoryTheory.DerivedMonoidal

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

open MonoidalCategory

variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The canonical signed symmetry, packaged before specialization to sheaves.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym). -/
noncomputable def canonicalTensorSymmetry :
    curriedTensor (DerivedCategory C) ≅ (curriedTensor (DerivedCategory C)).flip :=
  letI : BraidedCategory (DerivedCategory C) := by exact braidedCategory' C
  BraidedCategory.curriedBraidingNatIso (DerivedCategory C)

end DerivedCategory

namespace AlgebraicGeometry.Etale

/-- The canonical symmetry of the unbounded derived tensor bifunctor, natural in both variables.
Source: Stacks Project, Tag 06YU (blueprint: lem-kun-tensor-sym).

Construction: the homotopy-category braiding is the signed swap in bidegree `(p,q)`, with
sign `(-1)^(p*q)`. Descend that braiding through the K-flat localization using
`DerivedMonoidal.braidingNatTrans`, and assemble its natural isomorphism of curried bifunctors.
The characterization `DerivedMonoidal.braiding_hom_μ` identifies the descended map on K-flat
representatives with precisely that signed swap. -/
noncomputable def derivedTensorSymmetry
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) : derivedTensor A T ≅ (derivedTensor A T).flip :=
  DerivedCategory.canonicalTensorSymmetry (Sheaf T.smallEtaleTopology A)

end AlgebraicGeometry.Etale
