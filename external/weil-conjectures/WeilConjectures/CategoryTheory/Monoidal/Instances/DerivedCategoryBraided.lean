/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!
# The braiding of the derived tensor product

For a braided Grothendieck abelian category `C` with functorial flat resolutions, this file
names the braiding `DerivedCategory.braidedCategory' C` of the derived tensor product on
`DerivedCategory C`, whose existence is `DerivedCategory.nonempty_braidedCategory`: the braiding
of `C`, with the Koszul sign rule on complexes, descended along K-flat resolutions
(`CategoryTheory.DerivedMonoidal.braidedCategory'`).

## Implementation notes

`DerivedCategory.braidedCategory'` is not an instance, since other braidings of derived categories
are assumed as instances elsewhere (for instance `AlgebraicGeometry.ProEtale.DerivedBraiding`).
It is meant to be used as a local instance. It is stated for a general `C`: instantiating it at a
concrete sheaf category is cheap, while elaborating `DerivedMonoidal.braidedCategory'` directly at
such a category makes the kernel compare two elaborations of the monoidal structure.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_braidedCategory : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The braiding of the derived tensor product on `DerivedCategory C`: the braiding of `C`, with
the Koszul sign rule on complexes, descended along K-flat resolutions. -/
@[instance_reducible]
noncomputable def braidedCategory' : BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory' Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end DerivedCategory
