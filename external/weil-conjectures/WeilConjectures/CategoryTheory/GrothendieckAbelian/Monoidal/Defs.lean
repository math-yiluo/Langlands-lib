/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The monoidal structure on sheaf categories over an essentially small site

The K-flat left derivability structure used to derive the pullback `g^*` on étale
sheaves requires the sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product preserves colimits, and to admit
functorial flat resolutions. The files of this folder supply each of these, so that the
derived pullback only takes hypotheses on the coefficient category `A`.

Nothing in this folder is specific to the étale site: as in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`, everything is stated for an
arbitrary site `C` with `Hom`-types in the universe `u` and objects in `u + 1` which is
essentially small in `u + 1`, and a Grothendieck abelian coefficient category `A` with
`Hom`-types in `u + 1`. The small étale site and the small pro-étale site are such sites,
so the étale and pro-étale instances are obtained from the general ones by `inferInstance`.

This file provides the monoidal structure itself, from
`CategoryTheory.Sheaf.monoidalCategory` (sheafification of the objectwise tensor
product of presheaves), together with its braiding
(`CategoryTheory.Sheaf.braidedCategory`). Their inputs are the sheafification (from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`) and the monoidality of
the class `W` of sheafification-inverting morphisms of presheaves.

That monoidality is `CategoryTheory.GrothendieckTopology.W.monoidal`: for a *closed
braided* coefficient category `A`, the class `W` is stable under tensoring on either
side, because tensoring by `F` is left adjoint to the internal hom `[F, -]`, which
preserves sheaves (`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`), and the
braiding exchanges the two sides. This replaces the earlier stalkwise argument, which
required `A` to be concrete with a limit- and filtered-colimit-preserving forgetful
functor and could not be carried out with the coefficient category at `Type (u + 1)`:
mathlib's stalkwise criterion `ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`
wants a conservative family of `Point.{u + 1}`-points of the small étale site, while
mathlib only supplies `Point.{u}`-points. No concreteness hypothesis on `A` is left in
this folder.

The enriched-hom hypotheses of `GrothendieckTopology.W.monoidal` — the ends
`HasEnrichedHom A F₁ F₂` and `HasFunctorEnrichedHom A F₁ F₂` for presheaves `F₁ F₂` on
`C` — are not assumed: they are limits over a category with objects in `u + 1` and
`Hom`-types in `u`, hence of size `u + 1`, which a Grothendieck abelian category with
`Hom`-types in `Type (u + 1)` has by `CategoryTheory.IsGrothendieckAbelian.hasLimits`.
This is exactly where the universe constraint on the site is used.

Mathlib deliberately does not make `Sheaf.monoidalCategory` an instance, because for a
general coefficient category it can clash with a monoidal structure coming from chosen
finite products. No such clash arises here: the coefficient categories of this
development are abelian, so `Sheaf J A` is abelian as well and carries no cartesian
monoidal structure — its finite products are biproducts, for which mathlib registers no
`MonoidalCategory` instance. The two instances of this file are therefore global.

The preadditivity of this monoidal structure needs no transport of its own: it is
`CategoryTheory.Sheaf.monoidalPreadditive` of
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`, which applies to any sheaf
category. The remaining transports are in the sibling files `TensorColimits` and
`FlatResolution` of this folder; the latter is still recorded with `sorry`.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/- The monoidal structure on the coefficient category. It is assumed *closed* and
*braided*: closedness makes tensoring by a fixed presheaf a left adjoint whose right
adjoint preserves sheaves, hence makes the class of sheafification-inverting morphisms
stable under tensoring on the left, and the braiding transports this to the right. Both
hold, and are mathlib instances, in the intended application `A = ModuleCat.{u + 1} Λ`
with `Λ` a commutative ring — which is even symmetric monoidal closed, and covers
`A = Ab.{u + 1}` through `Λ = ℤ`. -/
variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- The monoidal structure on `A`-valued sheaves on an essentially small site, induced by
a monoidal structure on the coefficient category `A`: the sheafification of the objectwise
tensor product of presheaves. -/
noncomputable instance monoidalCategory_sheaf_of_essentiallySmall :
    MonoidalCategory (Sheaf J A) :=
  Sheaf.monoidalCategory _ _

/-- The monoidal structure `monoidalCategory_sheaf_of_essentiallySmall` is
`CategoryTheory.Sheaf.monoidalCategory` for any proof that `J.W` is monoidal. Results stated
for `Sheaf.monoidalCategory` under a hypothesis `(J.W (A := A)).IsMonoidal`, such as the oplax
monoidal structure on the pullback of étale sheaves, therefore apply to this instance. -/
lemma monoidalCategory_sheaf_of_essentiallySmall_eq [(J.W (A := A)).IsMonoidal] :
    monoidalCategory_sheaf_of_essentiallySmall A J = Sheaf.monoidalCategory J A :=
  rfl

/-- The braiding of the monoidal structure on `A`-valued sheaves on an essentially small
site, induced by the braiding of the coefficient category `A`. -/
noncomputable instance braidedCategory_sheaf_of_essentiallySmall :
    BraidedCategory (Sheaf J A) :=
  Sheaf.braidedCategory _ _

/-- The monoidal structure on `A`-valued sheaves on an essentially small site is symmetric
when `A` is. -/
noncomputable instance symmetricCategory_sheaf_of_essentiallySmall {A : Type u'}
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] :
    SymmetricCategory (Sheaf J A) :=
  Sheaf.symmetricCategory _ _


end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- The monoidal structure on `A`-valued étale sheaves: the instance above applied to the
essentially small small étale site. -/
noncomputable instance Etale.sheafMonoidalCategory :
    MonoidalCategory (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

/-- The braiding of the monoidal structure on `A`-valued étale sheaves: the instance above
applied to the essentially small small étale site. -/
noncomputable instance Etale.sheafBraidedCategory :
    BraidedCategory (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

/-- The monoidal structure on `A`-valued pro-étale sheaves: the instance above applied to
the essentially small small pro-étale site. -/
noncomputable instance ProEtale.sheafMonoidalCategory :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

/-- The braiding of the monoidal structure on `A`-valued pro-étale sheaves: the instance
above applied to the essentially small small pro-étale site. -/
noncomputable instance ProEtale.sheafBraidedCategory :
    BraidedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

/-- The symmetric structure on `A`-valued pro-étale sheaves, when `A` is symmetric. -/
noncomputable instance ProEtale.sheafSymmetricCategory {A : Type u'} [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalClosed A] :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance


end AlgebraicGeometry
