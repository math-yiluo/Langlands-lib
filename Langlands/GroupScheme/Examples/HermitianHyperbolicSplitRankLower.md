# Isotropic subspaces and actual Hermitian split-rank lower bounds

This internal construction transports the closed split tori on hyperbolic
coordinates back to a supplied all-test matrix presentation of the original
group. It uses the full Hermitian pairing in every characteristic.

The rank results assume a separable quadratic field extension, an arbitrary
finite coordinate index type, and an affine group scheme locally of finite
type over the base field with a supplied natural matrix presentation on every
test scheme. The base and extension fields have the same arbitrary universe;
the coordinate index type may have an independent universe. No restriction on
the middle block or lower bound on the ambient dimension is required.

`adjointGL` packages the conjugate transpose of an invertible matrix as an
invertible matrix. `Form.pullback H P` has the actual Gram matrix
`adjoint(P) * H.gram * P`; its Hermitian symmetry follows by reversing products
under adjoint. `Presentation.pullback` uses the inverse congruence to transport
the natural presentation on every test scheme.

`Presentation.planes_le_splitRank` starts with an actual hyperbolic
decomposition of the original pairing. Its coordinate matrix pulls the Gram
form back to the hyperbolic block matrix, with the remaining block evaluated
from the original pairing. Reindexing exposes those blocks, and the previously
constructed closed split torus gives the number of hyperbolic planes as a lower
bound on the original group's actual `splitRank`.

`Presentation.finrank_le_splitRank` obtains such a decomposition from each
actual totally isotropic subspace. Nondegeneracy of the linear-first pairing
follows from nonsingularity of the stored Gram matrix. Thus no nondegeneracy
premise is added to the presentation. `wittIndex_le_splitRank` applies the
result to a subspace attaining the Witt index, whose existence is supplied by
the pairing interface.

The provenance is derived internal linear algebra and transport, using
`HermitianHyperbolicDecomposition`, `HermitianHyperbolicGramCoordinates`,
`HermitianHyperbolicSplitTorus`, `HermitianMatrixNondegenerate` and the
matrix-presentation interfaces. This unit does not claim the upper bound or the
complete attained split-rank comparison.
