# Geometric reducedness from algebraically closed base changes

`Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedStatement.{u}` is a
proposition definition (`def … : Prop`); this module states it without proof.
For all schemes `X Y : Scheme.{u}` in one arbitrary universe and every morphism
`f : X ⟶ Y`, it asserts: if for every algebraically closed field `K : Type u`
and every morphism `y : Spec K ⟶ Y` the fibre product `pullback f y` is reduced,
then `GeometricallyReduced f`.

## The reused definitions

Nothing is redefined; every notion is an existing Mathlib definition.

- `GeometricallyReduced f` is Mathlib's class
  `AlgebraicGeometry.GeometricallyReduced`
  (`Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean`), whose single field
  is `geometrically IsReduced f`. By the definition of
  `AlgebraicGeometry.geometrically`
  (`Mathlib/AlgebraicGeometry/Geometrically/Basic.lean`), this says: for every
  field `K : Type u`, every morphism `Spec K ⟶ Y` and every scheme `Z` forming a
  pullback square with `f` and that morphism, `Z` is reduced. Since reducedness
  is invariant under isomorphism, Mathlib's
  `geometrically_iff_of_isClosedUnderIsomorphisms` shows that this is the same
  as `pullback f y` being reduced for every field `K : Type u` and every
  `y : Spec K ⟶ Y`. The fields range over `Type u`, the universe of the schemes.
- `IsReduced` applied to a scheme is Mathlib's `AlgebraicGeometry.IsReduced`:
  the ring of sections over every open subset is reduced.
- `IsAlgClosed K` is Mathlib's algebraic closedness: every polynomial over `K`
  splits.
- `Spec (.of K)` is the spectrum of `K` as a commutative ring, and
  `pullback f y` is the chosen categorical fibre product `X ×_Y Spec K` in the
  category of schemes.

## Exactly what is and is not assumed

There is no hypothesis on `X`, `Y` or `f`: no finiteness, separatedness,
quasi-compactness or noetherian condition, and `Y` need not be the spectrum of
a field. The only hypothesis is the displayed one. It concerns algebraically
closed fields in `Type u` and arbitrary morphisms from their spectra to `Y`; the
conclusion concerns all fields in `Type u`, so the statement is the nontrivial
direction of the comparison. The converse is immediate from Mathlib's
definition and is not stated here. Only the global property is stated, not the
pointwise notion "geometrically reduced at `x`" of the Stacks Project.

## Provenance

This is a derived statement: a version, for a morphism to an arbitrary target
`Y`, of results in the Stacks Project, Chapter 33 (Varieties), Section 33.6
(Geometrically reduced schemes, Tag 035U).

- Definition 33.6.1 (Tag 035V): a scheme `X` over a field `k` is geometrically
  reduced over `k` if for every field extension `k'/k` all local rings of
  `X_{k'}` are reduced, that is, every `X_{k'}` is reduced. For `Y = Spec k`,
  morphisms `Spec K ⟶ Spec k` are field extensions `K/k`, so Mathlib's
  `GeometricallyReduced` agrees with this notion except that Mathlib quantifies
  only over fields `K : Type u`.
- Lemma 33.6.6 (Tag 0384): for a field extension `k'/k`, `X` is geometrically
  reduced over `k` if and only if `X_{k'}` is geometrically reduced over `k'`.
  Its proof uses Algebra, Lemma 10.164.2 (Tag 033F): if `R → S` is faithfully
  flat and `S` is reduced, then `R` is reduced.
- Lemma 33.6.3 (Tag 020I): over a perfect field, in particular an algebraically
  closed one, a reduced scheme is geometrically reduced.

Taking `k' = \bar k` an algebraic closure, Tags 0384 and 020I together give: `X`
is geometrically reduced over `k` as soon as `X_{\bar k}` is reduced. (In
characteristic `p > 0` this is also the implication (6) ⇒ (1) of Lemma 33.6.4,
Tag 035X.) The Lean statement applies this to every fibre `pullback f y` of `f`
over a field-valued point `y : Spec K ⟶ Y`. The base change of that fibre to an
algebraic closure of `K` is, by pullback pasting, the fibre of `f` over the
composite point of `Y`, which the hypothesis covers because it concerns every
algebraically closed field in `Type u` and every morphism from its spectrum to
`Y`. The morphism formulation over an arbitrary `Y` follows Mathlib's
definition. This paragraph describes the expected proof obligation; the present
module proves nothing.

Registered sources:

- `stacks-geometrically-reduced-schemes-section-035u-2026-10-30`: web snapshot
  of the whole Section 33.6 (Tag 035U) fetched on 2026-10-30, SHA-256
  `6435a4eaa6664fc49a44d8a086a01e582869c00f2377f660e077709e5df2f888`; it
  contains Definition 33.6.1 and Lemmas 33.6.3, 33.6.4 and 33.6.6.
- `stacks-geometrically-reduced-base-field-change-0384-2026-10-29`: web
  snapshot of Lemma 33.6.6 (Tag 0384) fetched on 2026-10-29, SHA-256
  `629ad4316b434e26c5d5ef34b8a59ba7bba9e61398bf44fd9bace33ca9e47c00`.
- `stacks-faithfully-flat-descent-reduced-033f-2026-10-29`: web snapshot of
  Algebra, Lemma 10.164.2 (Tag 033F) fetched on 2026-10-29, SHA-256
  `a978732f32e8b47c0fa9df0a6b4484641a5d86847f6980eebca7fb24b2e95a7f`.
