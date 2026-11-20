# Prime-to-the-characteristic power maps on geometric points of unipotent groups are bijective

`Langlands.GroupScheme.UnipotentPowerBijectiveStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`U : GroupScheme (Spec (CommRingCat.of k))` satisfy `IsAffineHom U.X.hom`,
`LocallyOfFiniteType U.X.hom` and `IsUnipotent U`. Let `e : ℤ` with
`(e : k) ≠ 0`. Then the map `x ↦ x ^ e` on the group of morphisms
`Over.mk (toAlgebraicClosure k) ⟶ U.X` is bijective.

The ingredients are existing declarations, used without change.

- `IsUnipotent U` and `toAlgebraicClosure k` are from
  [`Reductive.Basic`](../Reductive/Basic.md). `IsUnipotent U` says that every
  nonzero finite-dimensional matrix representation of `U` has a nonzero
  fixed vector; that module records it as Milne 6.45 (p.135).
  `toAlgebraicClosure k` is `Spec` of the algebra map
  `k → AlgebraicClosure k`.
- `Over.mk (toAlgebraicClosure k)` is `Spec (AlgebraicClosure k)` as a
  scheme over `Spec k`. A morphism from it to `U.X` over `Spec k` is a point
  of `U` with values in `AlgebraicClosure k`. These points form a group,
  because `U.X` is a group object (`open scoped CategoryTheory.MonObj`), and
  `x ^ e` is the integer power in that group.
- `IsAffineHom`, `LocallyOfFiniteType`, `AlgebraicClosure` and `Spec` are
  from Mathlib.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Lemma 15.2, p.303: "Let U be a unipotent algebraic group, and let e be an
  integer not divisible by the characteristic of k. Then the map
  x ↦ x^e: U(k^a) → U(k^a) is bijective."
- Its proof: "This is obviously true for G_a. A proper algebraic subgroup N
  of G_a is finite, and the map on N(k^a) is injective, and so it is
  bijective. As every unipotent group admits a filtration whose quotients
  are subgroups of G_a (see 14.21), and the functor U ⇝ U(k^a) is exact
  (5.48), the general case follows."
- Chapter 15 opening, p.302: "Recall that all algebraic groups are affine
  over the base field k."
- Notation, p.3: "An algebraic scheme over k (or algebraic k-scheme) is a
  scheme of finite type over k." Definition 1.1, p.6, defines an algebraic
  group over k as a group object in the category of algebraic schemes over
  k.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Lemma 15.2 and its proof
on p.303 and the quoted p.3 sentence with the same words. Its Chapter 15
opening, on p.302, reads "Recall that all algebraic groups are affine."

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for 1.1, 6.45, 15.2, or pp.3, 6,
302 or 303.

## Derivation from the source

- **Unipotent algebraic group.** By Definition 1.1 and p.3, Milne's
  algebraic group over `k` is a group scheme of finite type over `k`; in
  Chapter 15 it is also affine. The
  hypotheses `IsAffineHom U.X.hom` and `LocallyOfFiniteType U.X.hom` say
  that `U` is affine of finite type over `k`. Unipotence is `IsUnipotent U`.
- **The integer `e`.** "`e` is not divisible by the characteristic of `k`"
  is `(e : k) ≠ 0`. If `k` has characteristic `p > 0`, the image of `e` in
  `k` vanishes exactly when `p` divides `e`. If `k` has characteristic zero,
  it vanishes exactly when `e = 0`, the only integer divisible by `0`.
- **The points `U(k^a)`.** `k^a` is Mathlib's `AlgebraicClosure k`. The
  group `U(k^a)` is the group of morphisms
  `Over.mk (toAlgebraicClosure k) ⟶ U.X` of schemes over `Spec k`, with the
  group law induced by the group object `U`.
- **Conclusion.** "The map x ↦ x^e is bijective" is
  `Function.Bijective (fun x => x ^ e)` on this group.
- **Universes.** One universe `u` is used for the field and the scheme.
  This is a formalization convention.

## Related Library results

`Langlands.GroupScheme.exists_hasUniformPowerExponent_of_isUnipotent` (from
[`Rational.UnipotentPointsExponent`](../Rational/UnipotentPointsExponent.md))
proves, in characteristic `p > 0`, that an affine, locally finite type
unipotent group has an exponent `p ^ r` that kills every point over every
test scheme. Characteristic zero is not covered by that theorem.
