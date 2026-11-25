# Split rank of isotropic Cayley automorphism groups

`Langlands.GroupScheme.IsotropicCayleyAutomorphismRankStatement` is an
unproved proposition over every field `K`, in every characteristic. It
quantifies over an actual `CayleyDatum K`, a group scheme `H` over
`Spec K`, and a morphism from `H` into the actual general linear group
in dimension eight.

The first hypothesis is `c.IsAutomorphismRepresentation iH`. This
requires a closed immersion whose range on every test scheme is exactly
the invertible matrices fixing the identity and preserving the extended
bilinear multiplication of `c`. Thus the hypothesis identifies the full
algebra automorphism functor, including nonreduced tests. It supplies no
split rank or splitness assumption. The second hypothesis supplies an
actual nonzero vector at which `c.norm` is zero. The conclusion is the
equality `splitRank H = 2` in `ℕ∞`, using the Library's supremum of
dimensions of actual closed split subtori.

This is a derived consequence of Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions*, over arbitrary fields:

- Theorem 33.17, printed pp.459–460 / PDF pp.482–483, identifies the
  eight-dimensional unital composition data as a Cayley algebra.
- Theorem 33.19 and Proposition 33.23, printed pp.460–461 / PDF
  pp.483–484, classify Hurwitz algebras by their norms and make an
  isotropic norm hyperbolic.
- The discussion on printed p.462 / PDF p.485 therefore identifies every
  isotropic Cayley algebra with the split Cayley algebra and identifies
  its automorphism group as split of type G2.
- Theorem 25.14, printed p.360 / PDF p.383, identifies the automorphism
  group of the split Cayley algebra with the split simple group of
  type G2. Its reference explicitly includes a proof over arbitrary
  fields.

These facts give the intended route to the rank equality: construct the
algebra isomorphism to a split Cayley model, induce an isomorphism of
the full represented automorphism group schemes, and compare the actual
split rank with the rank two root datum of split G2. None of those
steps is proved in this module. In particular, an identification of
`K`-points alone would not discharge the stated all-test hypothesis or
the required scheme-level comparison.

There is no local-field hypothesis or restriction on field
characteristic. The characteristic restriction for the cohomological
invariants discussed later on printed p.462 does not apply to the
preceding split-algebra and automorphism-group facts. The retained
official author errata and relevant page-sorted unofficial comments
were checked; the flagged reference in the proof of Proposition 33.6
is not used. This proposition neither constructs a representing group
nor proves a local rank-one exclusion.
