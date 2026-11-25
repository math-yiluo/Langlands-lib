/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!

# The tensor product of sheaves on an essentially small site preserves colimits

The K-flat left derivability structure requires the sheaf category to interact well with
the coproducts defining the tensor product of complexes and with `ℤ`-indexed colimits. All
of these conditions — `GradedObject.HasTensor₄ObjExt`,
`GradedObject.HasGoodTensor₁₂Tensor`, `GradedObject.HasGoodTensorTensor₂₃` and the
preservation of `ℤ`-indexed colimits in each variable — unfold to the statement that
`tensorLeft X` or `tensorRight X` preserves a colimit of size `0`. This file proves the
single instance they all follow from, for the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

The proof is Day's reflection theorem
(`CategoryTheory.Monoidal.Reflective.monoidalClosed`), which makes `Sheaf J A` monoidal
closed and hence `tensorLeft X` a left adjoint. Its inputs are all available for an
arbitrary site `C` with `Hom`-types in the universe `u` and objects in `u + 1` which is
essentially small in `u + 1`, exactly as in the sibling file `Defs`:

* the presheaf category `Cᵒᵖ ⥤ A` is monoidal closed for the objectwise monoidal
  structure, by `CategoryTheory.MonoidalClosed.FunctorCategory.monoidalClosed`, whose
  internal hom is the enriched functor hom. This is a *scoped* instance, hence the
  `open scoped` below. Its enriched-hom side conditions are limits of size `u + 1`,
  supplied by `CategoryTheory.IsGrothendieckAbelian.hasLimits` exactly as for the
  monoidality of `W` in the sibling file `Defs`;
* the presheaf category is *symmetric* monoidal, which is what Day's theorem asks of the
  ambient category and is the only reason `A` is assumed symmetric rather than merely
  braided here — this is the sole extra hypothesis this file adds to those of `Defs`;
* `presheafToSheaf` is monoidal and `sheafToPresheaf` is fully faithful, both instances
  of `CategoryTheory.Sheaf.monoidalCategory`'s file for the monoidal structure of `Defs`.

Note that the resulting `monoidalClosed_sheaf_of_essentiallySmall` is over the monoidal
structure of `Defs` (the sheafification of the objectwise tensor product), *not* over a
cartesian one: mathlib's `instMonoidalClosedSheafOfHasSheafifyOfFunctorOpposite` produces a
monoidal closed structure for the cartesian tensor on a full monoidal subcategory of
presheaves, which is a different instance and moreover unavailable here, since the
coefficient categories of this development are abelian and a non-trivial additive category
is never cartesian closed.

The small étale site and the small pro-étale site are such sites, so the étale and
pro-étale instances at the end of the file are obtained from the general ones by
`inferInstance`.

## Main results

- `CategoryTheory.GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall`: the category
  of `A`-valued sheaves on an essentially small site is monoidal closed.
- `CategoryTheory.GrothendieckTopology.preservesColimitsOfSize_tensorLeft_sheaf_of_essentiallySmall`
  and its right variant: tensoring with a fixed sheaf preserves colimits of size `0`.
- `AlgebraicGeometry.Etale.sheafMonoidalClosed`,
  `AlgebraicGeometry.Etale.preservesColimitsOfSize_tensorLeft_sheaf`: the special cases for
  the small étale site.
- `AlgebraicGeometry.ProEtale.sheafMonoidalClosed`,
  `AlgebraicGeometry.ProEtale.preservesColimitsOfSize_tensorLeft_sheaf`: the special cases
  for the small pro-étale site.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped MonoidalClosed.FunctorCategory

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/- The monoidal structure on the coefficient category, as in the sibling file `Defs`,
except that the braiding is strengthened to a symmetry: Day's reflection theorem is
stated for a symmetric ambient category. This still holds, and is a mathlib instance, in
the intended application `A = ModuleCat.{u + 1} Λ` with `Λ` a commutative ring. -/
variable [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]

/-- The category of `A`-valued sheaves on an essentially small site is monoidal closed,
for the monoidal structure `monoidalCategory_sheaf_of_essentiallySmall` of the sibling file
`Defs`.

This is Day's reflection theorem applied to the sheafification adjunction
`presheafToSheaf ⊣ sheafToPresheaf`: the left adjoint is monoidal, the right adjoint is
fully faithful, and the presheaf category is symmetric monoidal closed. -/
noncomputable instance monoidalClosed_sheaf_of_essentiallySmall :
    MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)

/-- Tensoring on the left with a fixed `A`-valued sheaf on an essentially small site
preserves colimits of size `0`, since it is left adjoint to the internal hom of
`monoidalClosed_sheaf_of_essentiallySmall`. Together with the braiding this gives every
compatibility between the tensor product of sheaves and colimits that the K-flat left
derivability structure asks for. -/
instance preservesColimitsOfSize_tensorLeft_sheaf_of_essentiallySmall (X : Sheaf J A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

/-- Tensoring on the right with a fixed `A`-valued sheaf on an essentially small site
preserves colimits of size `0`, by
`preservesColimitsOfSize_tensorLeft_sheaf_of_essentiallySmall` and the braiding. -/
instance preservesColimitsOfSize_tensorRight_sheaf_of_essentiallySmall (X : Sheaf J A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) where
  preservesColimitsOfShape := ⟨inferInstance⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]

/-- The category of `A`-valued étale sheaves is monoidal closed: the instance above applied
to the essentially small small étale site. -/
noncomputable instance Etale.sheafMonoidalClosed :
    MonoidalClosed (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

/-- Tensoring on the left with a fixed `A`-valued étale sheaf preserves colimits of size
`0`: the instance above applied to the essentially small small étale site. -/
instance Etale.preservesColimitsOfSize_tensorLeft_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

/-- Tensoring on the left with a fixed `A`-valued étale sheaf is right exact, as a particular
case of `Etale.preservesColimitsOfSize_tensorLeft_sheaf`. -/
instance Etale.preservesFiniteColimits_tensorLeft_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesFiniteColimits (tensorLeft X) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- Tensoring on the right with a fixed `A`-valued étale sheaf preserves colimits of size
`0`: the instance above applied to the essentially small small étale site. -/
instance Etale.preservesColimitsOfSize_tensorRight_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  inferInstance

/-- The category of `A`-valued pro-étale sheaves is monoidal closed: the instance above
applied to the essentially small small pro-étale site. -/
noncomputable instance ProEtale.sheafMonoidalClosed :
    MonoidalClosed (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

/-- Tensoring on the left with a fixed `A`-valued pro-étale sheaf preserves colimits of
size `0`: the instance above applied to the essentially small small pro-étale site. -/
instance ProEtale.preservesColimitsOfSize_tensorLeft_sheaf
    (X : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

/-- Tensoring on the left with a fixed `A`-valued pro-étale sheaf is right exact, as a
particular case of `ProEtale.preservesColimitsOfSize_tensorLeft_sheaf`. -/
instance ProEtale.preservesFiniteColimits_tensorLeft_sheaf
    (X : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesFiniteColimits (tensorLeft X) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- Tensoring on the right with a fixed `A`-valued pro-étale sheaf preserves colimits of
size `0`: the instance above applied to the essentially small small pro-étale site. -/
instance ProEtale.preservesColimitsOfSize_tensorRight_sheaf
    (X : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  inferInstance

end AlgebraicGeometry
