# Conjugation on the coordinate span of a dense rational subgroup

This internal construction combines `GeneralLinearCoordinateConjugation` with
the published `DenseRationalStability` interface and the split-coordinate
construction in `NormalFixedRepresentation`. The coordinate-conjugation pair is
a separate prerequisite, ported unchanged with this module.

For any matrix representation over a commutative ring, `coordinateConjugation`
is the actual group-scheme homomorphism acting by conjugation on both the matrix
and inverse-matrix coordinate summands. Its point matrices on every scheme test
and its rational matrices are the existing coordinate-conjugation matrices.
The action on the coordinate values of a rational point is the coordinate vector
of its conjugate in the original group.

Over an arbitrary field in universe `u`, `subgroupCoordinateSpan` is the linear
span of the matrix and inverse-matrix values of a rational subgroup. Each element
of the subgroup's actual normalizer preserves the set of generating values, hence
preserves its entire linear span by linearity and span induction. Faithfulness
of the original representation is not required for these assertions.

`ConjugationSubrepresentation` records a finite-dimensional actual representation,
an inclusion and a retraction whose product is the identity, membership of each
inclusion column in the coordinate span, the projection identity on that span,
the intertwining identity on all scheme tests, and the exact rational matrix
formula in these split coordinates.

If the original group scheme is reduced and the specified subgroup family is
Zariski dense, `nonempty_conjugationSubrepresentation` constructs this record.
It chooses split coordinates for the span. Subgroup elements preserve that span
because they belong to its normalizer. Applying the projection to the image of
each inclusion column gives the coordinate stability equation on the dense family.
The published detection theorem extends this equation to every scheme test,
including nonreduced tests. The existing `restrictCoordinates` construction then
gives the actual representation and intertwining law; the canonical isomorphism
of global sections over the field spectrum gives the rational matrix formula.
`conjugationSubrepresentation` chooses one such record.

This module constructs the restricted action. Identifying its kernel with the
scheme center, bounding the normalizer image, and proving the normalizer
theorem it serves are done in other modules: `ConjugationKernel`,
`ConjugationBounded` and `DenseBoundedNormalizerAdjointProof`
(`denseBoundedNormalizerAdjoint`).
