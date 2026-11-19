# Split unipotence descends along separable extensions

`Langlands.GroupScheme.SeparableSplitUnipotentDescentStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`IsUnipotent G`. Let `K : Type u` be a field with `[Algebra k K]` and
`Algebra.IsSeparable k K`, and write `G_K` for
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`.
If `RelativeRoot.IsSplitUnipotent G_K`, then
`RelativeRoot.IsSplitUnipotent G`.

The ingredients are existing declarations, used without change.

- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector (Milne 6.45).
- `RelativeRoot.IsSplitUnipotent H` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that `H` has a finite series `H = H_0 ⊃ H_1 ⊃ ⋯ ⊃ H_n` ending in the
  trivial group, in which each `H_{i+1}` is a smooth connected closed
  subgroup that is normal in `H_i`, and `H_i` has an fppf quotient by
  `H_{i+1}` that is a one-dimensional vector group (isomorphic to `G_a`).
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`.
- `Algebra.IsSeparable k K` (Mathlib) says that every element of `K` is
  separable over `k`: its minimal polynomial over `k` is separable. The zero
  polynomial is not separable, so every element is algebraic over `k`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- 14.65, p.299: "A unipotent group G over k is split if it splits over a
  separable field extension k′ of k."
- Definition 14.61, p.299: "A unipotent algebraic group G over k is split
  if it admits a subnormal series each of whose quotients is isomorphic to
  G_a."
- 14.62, p.299: "A split unipotent algebraic group is automatically smooth
  and connected (8.1). If G is split over k, then G_{k′} is split over k′
  for all fields k′ containing k."
- Notations, p.3: "a separable extension is a separable algebraic
  extension."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every
  nonzero representation of G has a nonzero fixed vector."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."

Milne's argument, for orientation only: one reduces to `G` elementary and
`k′` finite over `k`. Then a `k`-basis `x_1, …, x_n` of `k′` is a basis of
`k′_σ[F]` over `k_σ[F]` (this uses separability), the module `P(G_{k′})` is
free over `k′_σ[F]`, so `P(G)` is a submodule of a free `k_σ[F]`-module and
hence free (14.50).

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states 14.65, Definition
14.61 and 14.62 on printed p.299 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for pp.3, 135, 279 or 299.

## Derivation from the source

- **The group.** Milne's unipotent group over `k` is an algebraic group,
  that is, a group scheme of finite type over `k`, affine by the Chapter 14
  convention. The statement assumes `LocallyOfFiniteType G.X.hom` and
  `IsAffineHom G.X.hom`; an affine morphism is quasi-compact, so `G` is of
  finite type over `k`. Unipotence (6.45) is `IsUnipotent G`.
- **Separable field extension.** By the convention on p.3, a separable field
  extension of `k` is a separable algebraic extension. This is a field `K`
  with an algebra structure over `k` and `Algebra.IsSeparable k K`, which
  includes algebraicity. The field `K` lies in the universe `u` of `k`. This
  loses nothing: every algebraic extension of `k` embeds into
  `AlgebraicClosure k`, which lies in that universe.
- **Split.** Definition 14.61 asks for a subnormal series whose quotients
  are isomorphic to `G_a`. This is `RelativeRoot.IsSplitUnipotent`. Its
  additional requirements hold for every such series: by 14.62 a split
  unipotent group is smooth and connected, and so is each term of the
  series, which is itself split unipotent. Milne's quotient
  `G_i/G_{i+1}` is the target of a flat surjective homomorphism with kernel
  `G_{i+1}`, which the Library predicate records as an fppf quotient.
  "`G` splits over `K`" is `RelativeRoot.IsSplitUnipotent G_K` for the base
  change `G_K`.
- **Universes.** One universe `u` is used for the fields and the schemes.
  This is a formalization convention.
