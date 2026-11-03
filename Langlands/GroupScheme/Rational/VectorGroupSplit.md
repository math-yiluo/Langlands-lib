# Finite additive-group series for vector groups

For every field `k` in universe `u`, a group scheme with natural additive
coordinates of dimension `n` has `HasSplitSeries n`. In particular it satisfies
the existing `IsSplitUnipotent` predicate. The results include dimension zero and
all characteristics, without further geometric assumptions on the group.

The construction starts with the standard polynomial vector group.
`firstCoordinate` is its homomorphism to the one-dimensional vector group,
defined by the primitive polynomial `X 0`. The theorem
`coordinates_firstCoordinate` identifies this map on every scheme test.
The first coordinate together with the tail coordinates is a permutation of all
polynomial variables. The variable-renaming algebra isomorphism therefore makes
the evaluation map bijective. The existing primitive-coordinate quotient lemmas
give flatness, surjectivity and local finite presentation, and the kernel
equality is the equality with the range of the actual scheme-kernel inclusion.
These establish `isFppfQuotient_firstCoordinate` with the existing fppf quotient
definition.

`firstCoordinateKernelCoordinates` gives the actual scheme kernel natural
coordinates of dimension `n`. It first identifies kernel points with the
pointwise kernel of the homomorphism, then retains the tail coordinates.
Its inverse inserts a zero first coordinate. The coordinate formula verifies
that this point is in the kernel; the inverse laws follow from equality of all
coordinates. Naturality follows from pullback of global functions and the
associativity of composition. This construction applies to every scheme test,
including nonreduced ones.

The standard-model theorem `VectorGroup.hasSplitSeries` now follows by
induction. The zero-dimensional vector group has trivial points on every test,
so its identity homomorphism has trivial range. In the successor step the kernel
is smooth and connected by its natural vector coordinates. Its inclusion is a
closed immersion because the target one-dimensional vector group is affine
and therefore separated. The range is normal since the ambient vector-group
points commute. The fppf projection has the required one-dimensional vector
target. Transporting the induction hypothesis along the kernel's actual
vector-group isomorphism supplies its remaining series.

Finally, `IsVectorGroupOfDimension.hasSplitSeries` transports this standard
series through the actual isomorphism supplied by the published natural
coordinate comparison. Its split-unipotence corollary, and the analogous
corollary for an unspecified finite dimension, use the existing existential
definition of `IsSplitUnipotent`.

This is an internal consequence of the Library's polynomial vector group,
primitive-coordinate quotient, actual kernel, vector geometry and isomorphism
transport constructions. It supplies the finite additive-group series adapter;
the host maximal-torus conjugacy theorem and the separate structural existence
and linearization statements remain proof obligations.
