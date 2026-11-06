# Independence of ordered products of special segment heads

This internal supporting module proves `OrderedSegmentHeadProductIndependence`:
actual normalized products of supplied special segment heads are isomorphic when
their segment multisets agree and both segment enumerations satisfy the existing
nonprecedence ordering. It retains every occurrence, including repeated segments,
and includes rank zero. The proof uses no classification or head-existence
premise.

Equality of multisets first gives a bijection of the finite occurrence indices,
using the permutation-index API also used in the published
`TemperedBlockUniquenessReduction`. Each original occurrence receives the negative
of its position in the target enumeration as a real sorting weight. The proved
`finitePermutationSorting` theorem sorts those weights while preserving an
invariant: precedence ordering and an actual isomorphism from the original
induced product to the current one.

For an adjacent strict inversion, the two occurrences appear in opposite orders
in the current and target enumerations. If their segments were linked,
`Segment.IsLinked.precedes_or_precedes` would give precedence in one of the two
directions. The current ordering excludes one direction and the target ordering
excludes the other. Thus the pair is unlinked, and the published
`adjacentUnlinkedSegmentSwap` theorem gives the required actual isomorphism after
swapping it. The existing ordering-preservation lemma supplies the other part of
the invariant.

At the end, the map from current positions to target positions is a monotone
bijection of finite chains, hence an order isomorphism. Uniqueness of finite-chain
order isomorphisms identifies the segment lists. For equal segment lists, each
pair of supplied heads is isomorphic by comparison with the same canonical
segment head. Applying normalized induction to those actual block isomorphisms
identifies the products. Composing with the sorting invariant proves the result.
The same-list comparison is the head counterpart of the published socle helper
in `SegmentSocleProductComparison`.

The final helper `nonempty_langlandsQuotient_iso_of_multisegment_eq` proves only
the forward implication of the requested ordered classification, under the
explicit premise `OrderedMultisegmentHeadExistence`. It transports both supplied
weak quotient witnesses to the same product and applies the published comparison
of weak irreducible quotients of a source with a strong head. Neither supplied
quotient is assumed to satisfy kernel uniqueness. This conditional helper does
not prove head existence, the converse implication, or the unconditional
`OrderedMultisegmentHeadClassification` target. Independent field and
representation universes are preserved throughout.

The finite-occurrence matching step reuses
`Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq` in
`Langlands.Combinatorics.FiniteOccurrenceMatching`. The helper has the same
statement and proof as the formerly private copy.
