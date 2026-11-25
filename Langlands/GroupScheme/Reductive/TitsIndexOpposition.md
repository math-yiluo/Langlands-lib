# Opposition preserves the actual Tits index

For any field `k : Type u`, any affine group scheme of locally finite type over
`k`, and any actual `TitsIndexData d` for it, this internal construction supplies
`d.oppositionIndexEquiv : TitsIndexEquiv d d`. Its vertex permutation is the
canonical based representative of simultaneous minus identity on the full
character and cocharacter lattices. It preserves every integral Cartan entry,
the exact zero and distinguished subsets, and the action of every element of
`Gal(k_s/k)`. The permutation is involutive. The semisimplicity hypothesis is
carried by the supplied Tits data; there is no restriction on characteristic,
split rank, absolute type or simple connectedness.

`GaloisPinningData.opposite` retains the actual torus, its inclusion, root index
and full root datum. It replaces the base by its image under root-datum
negation. The published `RootPinning.ofSplitMaximalTorus` chooses the required
simple-root trivializations. `TitsIndexData.opposite` also retains the maximal
split torus and its maps, and negates the positive cocharacter. Genericity
follows by negating each nonzero relative-root pairing. Compatibility follows
from negative-base positivity and the same nonzero pairing. Thus this is
actual compatible Tits data, rather than an abstract proposed marked diagram.

The key comparison uses the published
`TitsIndexIndependence.exists_based_conj` between `d` and `d.opposite`. It
supplies a conjugating point, an actual torus isomorphism, and a root-datum
equivalence `epsilon` that carries the base to its negative and preserves zero
restriction. The underlying maximal torus is unchanged, so this point
normalizes it. The published normalizer-to-Weyl comparison identifies
`epsilon` with an element of the full integral Weyl group by equality of their
weight maps.

The composite of negation with `epsilon` preserves the original base. Since
negation is central and involutive, this composite differs from negation by
the Weyl element `epsilon`. Uniqueness of the based representative in that
Weyl coset identifies the composite with `d.oppositionAut`. Actual restriction
of a negated root is the negative of the original restriction, by additivity
of character composition and base-change descent. Consequently opposition
preserves zero restriction of every absolute root. Restricting to simple
vertices gives the zero-subset comparison and, by complement, the
distinguished-subset comparison.

The based projection is a group homomorphism and is the identity on based
automorphisms. Applying it to centrality and involutivity of negation proves
that opposition commutes with every based automorphism and is involutive.
In particular it commutes with each absolute Galois star automorphism. Root-
datum pairing preservation gives the Cartan comparison. These facts supply
all fields of `oppositionIndexEquiv`.

This is an internal consequence of the published actual-index independence,
normalizer-to-Weyl, based-projection and root-line constructions together with
the paired `RootDatumNegation` lattice construction. It is not a new
translation of a literature statement. It does not identify opposition in
any particular Dynkin numbering, determine the inner-type-A central marked
position, or prove the local rank-one enumeration.
