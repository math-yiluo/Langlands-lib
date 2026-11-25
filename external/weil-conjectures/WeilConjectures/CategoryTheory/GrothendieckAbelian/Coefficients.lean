/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!

# Coefficient categories for sheaves on the small sites

The six-functor files of this project work with sheaves on the small sites of `P`-schemes
over a scheme `U : Scheme.{u}` with values in a Grothendieck abelian category `A` with
`Hom`-types in the universe `u + 1`. Beyond Grothendieck abelianness of `A`, they need
sheafification of `A`-valued presheaves on these sites and on their localizations. These
sites have objects in `Type (u + 1)` and `Hom`-types in `Type u`, so they are essentially
`u + 1`-small, and sheafification with values in a Grothendieck abelian category of that size
exists for them by `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`,
which goes through the transfinite plus construction (see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`).

This file introduces the class `CategoryTheory.HasSmallSiteSheafify A` recording
sheafification of `A`-valued presheaves on every `u + 1`-small site. It is the single
hypothesis on the coefficient category, next to Grothendieck abelianness, that the
six-functor formalism assumes. It holds for the concrete categories `ModuleCat.{u + 1} Λ` and
`AddCommGrpCat.{u + 1}` by Mathlib's sheafification (see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`), and for every
Grothendieck abelian category of size `u + 1`.

## TODO

The class is scaffolding, not a permanent part of the API. It was introduced because Mathlib
only provides sheafification for *concrete* coefficient categories
(`CategoryTheory.HasSheafify` via `Mathlib/CategoryTheory/Sites/LeftExact.lean`, which needs
`PreservesLimits (forget A)`). The project now proves it for every Grothendieck abelian `A`
of size `u + 1`, and records this as the instance
`CategoryTheory.HasSmallSiteSheafify.of_isGrothendieckAbelian` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. So the class is now redundant:
it, and the `[HasSmallSiteSheafify A]` hypotheses in the files that carry it, should be
deleted.

## Main declarations

- `CategoryTheory.HasSmallSiteSheafify`: the class.
- `CategoryTheory.HasSmallSiteSheafify.hasSheafify_of_essentiallySmall`: the class gives
  sheafification on every essentially `u + 1`-small site, not only on the `u + 1`-small ones.
- `CategoryTheory.Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify`: for `A` Grothendieck
  abelian with `HasSmallSiteSheafify A`, the sheaf categories on essentially `u + 1`-small
  sites are again Grothendieck abelian.

-/

@[expose] public section

universe u' u v₂ u₂

namespace CategoryTheory

open Limits

/-- A category `A` with `Hom`-types in the universe `u + 1` has *small-site sheafification*
if `A`-valued presheaves on every `u + 1`-small site admit a left exact sheafification. This
is the case for the concrete Grothendieck abelian categories `ModuleCat.{u + 1} Λ` and
`AddCommGrpCat.{u + 1}`, and for every Grothendieck abelian category of size `u + 1`
(`CategoryTheory.HasSmallSiteSheafify.of_isGrothendieckAbelian`). The small sites of
`P`-schemes over a scheme in `Scheme.{u}`, and their localizations, are essentially
`u + 1`-small, so the class applies to them through
`CategoryTheory.HasSmallSiteSheafify.hasSheafify_of_essentiallySmall`. -/
class HasSmallSiteSheafify (A : Type u') [Category.{u + 1} A] : Prop where
  hasSheafify {C : Type (u + 1)} [Category.{u + 1} C] (J : GrothendieckTopology C) :
    HasSheafify J A

namespace HasSmallSiteSheafify

variable (A : Type u') [Category.{u + 1} A] [HasSmallSiteSheafify A]

/-- The class asks for sheafification on `u + 1`-small sites only, but it gives it on every
essentially `u + 1`-small site: sheafification transports along the equivalence with the small
model (`CategoryTheory.hasSheafifyEssentiallySmallSite`).

This is deliberately *not* an instance: its conclusion `HasSheafify J A` matches every
sheafification goal in the library. The sites this project needs it for get their own
instances in `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, keyed on the
small sites, so that instance search is not attempted on unrelated `HasSheafify` goals. -/
lemma hasSheafify_of_essentiallySmall {C : Type u₂} [Category.{v₂} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) : HasSheafify J A :=
  have := HasSmallSiteSheafify.hasSheafify (A := A)
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
  hasSheafifyEssentiallySmallSite J A

end HasSmallSiteSheafify

attribute [local instance] HasSmallSiteSheafify.hasSheafify_of_essentiallySmall in
/-- The category of `A`-valued sheaves on an essentially `u + 1`-small site is Grothendieck
abelian, for `A` Grothendieck abelian with small-site sheafification. -/
lemma Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall' J A

end CategoryTheory
