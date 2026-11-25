/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!

# Countable coproducts of sheaves on an essentially small site

The K-flat left derivability structure used to derive the pullback `g^*` on étale sheaves
computes the tensor product of complexes as a coproduct over the fibers of the total
degree map `(p, q) ↦ p + q` on `ℤ × ℤ`. These fibers are countable, so the hypothesis it
needs on the sheaf categories is `CategoryTheory.Limits.HasCountableCoproducts`.

That instance is mathlib's `CategoryTheory.Sheaf.instHasColimitsOfShape` (colimits of
sheaves are computed by sheafifying the colimit of the underlying presheaves), applied
once per countable shape. It is restated here because instance search does not find it
on its own: unifying a `Discrete` shape against the many `HasColimitsOfShape` instances
available for a sheaf category diverges, whereas naming `Sheaf.instHasColimitsOfShape`
discharges the goal instantly.

As everywhere in this folder the statement is for an arbitrary site with `Hom`-types in
the universe `u` and objects in `u + 1`, essentially small in `u + 1`, and a Grothendieck
abelian coefficient category `A` with `Hom`-types in `u + 1`; sheafification is then
available by `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`. The small
étale site and the small pro-étale site are such sites, so
`AlgebraicGeometry.Etale.hasCountableCoproducts_sheaf` and
`AlgebraicGeometry.ProEtale.hasCountableCoproducts_sheaf` are just instances of it.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Countable coproducts of `A`-valued sheaves on an essentially small site, computed by
sheafifying the coproduct of the underlying presheaves. This is mathlib's
`CategoryTheory.Sheaf.instHasColimitsOfShape`; see the module docstring for why it has to
be restated here. -/
instance (priority := high) hasCountableCoproducts_sheaf_of_essentiallySmall
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) :
    HasCountableCoproducts (Sheaf J A) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

/-- Countable coproducts of `A`-valued étale sheaves: the instance above applied to the
essentially small small étale site. -/
instance (priority := high) Etale.hasCountableCoproducts_sheaf :
    HasCountableCoproducts (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

/-- Countable coproducts of `A`-valued pro-étale sheaves: the instance above applied to the
essentially small small pro-étale site. -/
instance (priority := high) ProEtale.hasCountableCoproducts_sheaf :
    HasCountableCoproducts (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

end AlgebraicGeometry
