# Length detected by a finite family of exact functors

`Langlands.ExactFamilyLengthBoundStatement` is an internal algebraic bridge for
the general reductive rank-one length argument. It states an implication about
actual smooth complex representations of arbitrary topological groups.

Let `F i`, for a finite index type, be functors from smooth representations of
`G` to smooth representations of groups `H i`. Each functor must preserve actual
short exact sequences in the sense of
`Derivative.Mirabolic.MapsShortExactIntertwiners`. Let `A` be a smooth
representation, and let `b i` be natural numbers bounding the actual composition
lengths `repLength ((F i).obj A).representation`.

Assume that every actual irreducible subquotient `D` of `A` has a nonzero image
under at least one of the functors. The conclusion is
`HasCompositionLengthAtMost A.obj (∑ i, b i)`: an actual finite composition
series of `A` whose number of simple factors is at most the sum of the bounds.
The representation `A` is not assumed to have finite length. The group, family,
and representation-carrier universes are independent; every functor preserves
the chosen carrier universe. The finite family may be empty.

This statement is derived internal infrastructure, not a translation of a
separately cited source assertion. Its rationale is to measure a subrepresentation
by the sum of the lengths of its images under the exact functors. A nonzero
successive quotient has an irreducible subquotient, so detection should make
that measure strictly increase. The existing bounded-chain criterion then gives
the stated actual composition series. This file states the criterion; it does
not prove it.

All representation-theoretic inputs needed to apply this criterion to Jacquet
functors, including exactness, the stated bounds and detection, remain separate
proof obligations. This statement does not supply those inputs.
