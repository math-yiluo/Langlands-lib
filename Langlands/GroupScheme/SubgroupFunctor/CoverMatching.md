# Pairwise overlap comparisons imply all-test cover matching

This internal construction specializes the published `Descent.squareComparison`
to two members of an arbitrary scheme covering family. `overlapSquareIso`
identifies the two iterated pullbacks of the ambient group on their actual
scheme-theoretic fibre product. It is natural in every original group
homomorphism, and its inverse preserves the projection to the original group.

`isMatching_of_overlap_range_eq` assumes local group homomorphisms into the
pullbacks of the ambient group. On each pairwise overlap, it assumes equality of
their ranges after transporting the second ambient group through the inverse
of `overlapSquareIso`. These are subgroup functors on every test scheme, so
the equality includes nonreduced tests. It concludes precisely the
`CoverDescent.IsMatching` predicate used by closed subgroup cover descent.
No closedness, monomorphism, affineness or property of the cover maps is needed.

For a comparison between tests over different cover members, the proof maps the
first test into the pairwise overlap using its two structure maps. It restricts
the second local point to this overlap test and uses the pullback point
equivalence to apply the assumed range equality. The same equivalence returns
membership in the first local range. Preservation of the projection to the
original ambient group identifies this point with the point required by
`IsMatching`.

The provenance is internal: the only inputs are the existing pullback
comparisons, point equivalences, subgroup ranges and the definition of matching.
This module supplies no local subgroup existence or pairwise range equality.
