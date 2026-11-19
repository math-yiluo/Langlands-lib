# Split solvable groups are trigonalizable

`Langlands.GroupScheme.SplitSolvableTrigonalizableStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `[Smooth G.X.hom]`,
`[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`. Then:

1. `IsSplitSolvableGroupScheme G → IsTrigonalizable G`; and
2. if `PerfectField k`, then `IsTrigonalizable G → IsSplitSolvableGroupScheme G`.

The ingredients are existing declarations, used without change.

- `IsSplitSolvableGroupScheme G` (from [`SplitSolvable`](../SplitSolvable.md))
  says that `G` is smooth, affine, connected and solvable
  (`IsSolvableGroupScheme`, from [`Absolute.Borel`](../Absolute/Borel.md)),
  and that it has a finite series `G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_n` ending in the
  trivial group, in which each `G_{i+1}` is a smooth connected closed
  subgroup that is normal in `G_i`, and `G_i` has an fppf quotient by
  `G_{i+1}` isomorphic to `G_a` (a one-dimensional vector group) or to
  `G_m`.
- `IsTrigonalizable G` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero vector spanning a stable line. This is Milne's Definition 16.1, as
  recorded in that module.
- `PerfectField k`, `Smooth` and `IsAffineHom` are from Mathlib;
  `ConnectedSpace G.X.left` says that the underlying topological space of
  `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 16.52, p.343: "Let G be a smooth connected algebraic group
  over k. If G is split solvable, then it is trigonalizable, and the
  converse is true when k is perfect."
- Section 16g, p.343: "Recall (6.33) that a solvable algebraic group is
  said to be split if it admits a subnormal series with quotients
  isomorphic to G_a or G_m. Every split solvable algebraic group is smooth
  and connected."
- Definition 6.33, p.132: "A solvable algebraic group G over k is split if
  it admits a subnormal series G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_n = e such that each
  quotient G_i/G_{i+1} is isomorphic to G_a or to G_m."
- Definition 16.1, p.324: "An algebraic group G is trigonalizable if every
  simple representation has dimension one."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

Milne's proof, for orientation only: if `G` is split solvable, it fixes a
point of the variety of maximal flags of a faithful representation (fixed
point theorem 16.51), so that representation is trigonalizable. If `k` is
perfect and `G` is trigonalizable, Corollary 16.24 applied to the split
torus `G/G_u` acting on `G_u` gives the split series.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Proposition 16.52 on
printed p.343, Definition 6.33 on p.132 and Definition 16.1 on p.324, with
the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.99, 132 or
343.
Their p.324 entry replaces "diagonalizable" with "trigonalizable" in the
last sentence of the first paragraph of Chapter 16; it does not concern
Definition 16.1 or the affineness sentence. The 2022 errata have no entry
for pp.99, 132, 324 or 343 (Definition 5.5 is on p.99 of both printings).

## Derivation from the source

- **The group.** Milne's smooth connected algebraic group is a group scheme
  of finite type over `k`, affine by the Chapter 16 convention. The
  statement assumes `Smooth G.X.hom` (so `G` is locally of finite type),
  `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`.
- **Split solvable.** Milne's split solvable group (Definition 6.33) has a
  subnormal series whose quotients are isomorphic to `G_a` or `G_m`. This is
  `IsSplitSolvableGroupScheme G`. Its additional requirements hold for every
  such series: the terms of the series are smooth and connected, because
  `G_{n-1}` is `G_a` or `G_m` and each `G_i` is an extension of `G_a` or
  `G_m` by `G_{i+1}`; and `G` is smooth, connected (p.343) and solvable.
  Milne's quotient `G_i/G_{i+1}` is the target of a flat surjective
  homomorphism with kernel `G_{i+1}` (Definition 5.5, p.99: "A homomorphism
  of algebraic groups is a quotient map if it is faithfully flat."), which the Library
  predicate records as an fppf quotient.
- **Trigonalizable.** Definition 16.1 is `IsTrigonalizable G`.
- **Perfect field.** "When `k` is perfect" is the hypothesis
  `PerfectField k` of part 2.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
