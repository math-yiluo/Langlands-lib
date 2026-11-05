# Vector lines from the actual intrinsic tangent bound

This internal construction identifies the Lie module of an actual representative
with its specified exact intrinsic Lie image. The remaining lemmas give a
conditional bridge from a nonzero tangent of dimension at most one to natural
one-dimensional vector coordinates. They do not prove the root-dimension bound
or the unconditional `AbsoluteRootVectorLineStatement`.

`RelativeRoot.representedLieImageEquiv` composes the published
`representedTangentLinearEquiv` with the equality expressing `HasLieImage`. It
uses the actual differential and changes no tangent vector.

For a smooth connected affine representative, `Lie.finiteDimensional_lieKernel`
makes its Lie module finite dimensional. `representedTangentLinearEquiv`
transports this finite-dimensional structure to the intrinsic tangent.
A nonzero intrinsic tangent of finrank at most one therefore has
finrank exactly one. Representability identifies this number with the
representative's Lie dimension. The published
`smoothConnectedRelativeDimension` and
`Lie.dimension_eq_of_smoothOfRelativeDimension` (imported through
`HomogeneousQuotientDimension`) give
`SmoothOfRelativeDimension 1`. Over a perfect field, the exact published
`perfectFieldOneDimensionalUnipotent` then supplies
`IsVectorGroupOfDimension U 1` for a unipotent representative. This conclusion
is the existing natural-coordinate predicate on all relative scheme tests,
including nonreduced tests.

`exists_rootVectorLine_of_tangent_le_one` applies this bridge to the published
`RelativeRoot.rootSubgroupRealization`. Root occurrence makes the full positive
weight span nonzero by `positiveWeightSpan_ne_bot`. The realization identifies
that span with the entire intrinsic root tangent, and supplies the actual closed,
smooth, connected unipotent representative. A bound on this entire tangent
remains an explicit hypothesis; a bound on just the first root weight space
would not suffice.

`absoluteRootVectorLine_of_tangentBound` assembles the exact existing absolute
target from such a bound for every root over every algebraically closed field.
It converts split maximal-torus data to maximal split-torus data using
`IsMaximalTorus.isMaximalSplitTorus`. No universe or characteristic restriction
is added. The original root functor, statement pair, and imports are unchanged.

The provenance is internal: this file combines the named published Library
results with the elementary finite-dimensional fact that a nonzero space of
dimension at most one has dimension one. It introduces no external mathematical
input. The geometric root-dimension bound is still a proof obligation.
