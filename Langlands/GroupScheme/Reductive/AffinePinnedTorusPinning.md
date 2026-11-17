# Torus conjugation and supplied simple pinning vectors

This internal consequence studies an actual point of the coordinate torus over
the coefficient ring of a supplied affine pinned model. The predicate
`TorusPermutesSimpleVectors` means that its actual adjoint action permutes the
chosen simple vectors with a bijection of the simple-root indices.

Over a nontrivial coefficient ring, a scalar multiple of one chosen simple
vector equals another only at the same root and with scalar one. The proof
projects the equation to a universal adjoint coefficient. Distinct roots have
distinct integral exponent weights, and each supplied vector is a nonzero
free generator of its weight line. Once the roots agree, injectivity of the
supplied line trivialization forces the scalar to be one.

The actual exponent weight equation therefore makes every simple-root
character of a point satisfying the predicate equal to one. This uses the
coefficient ring itself and retains its nilpotents. It does not yet derive the
predicate from a comparison preserving pinning or prove comparison uniqueness.
Combining these equations with the supplied reductivity, fibrewise maximality
and full coordinate root datum gives membership in the full centre functor.
This conclusion requires commutation after every relative refinement, not only
at points over the coefficient ring.
