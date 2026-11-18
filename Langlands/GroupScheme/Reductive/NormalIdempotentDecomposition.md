# Clopen decomposition of a normal idempotent

Worker 632, following the relative gluing input proposed by Worker 47.

`normalIdempotentDecomposition` constructs complementary opens of any base
scheme for an idempotent endomorphism of a reductive group with almost-simple
geometric fibres, provided its full pointwise image is normal. On the first
open the map is exactly the identity, and on the second it is exactly the
trivial map. These are equalities of actual group-scheme morphisms. The first
open is clopen. Conjugation equivariance on all relative test schemes implies
the required image normality.

Almost-simplicity of each geometric fibre reflects to its residue fibre by
the existing field-extension reflection theorem and the actual iterated
pullback comparison. The field normal-image idempotent dichotomy applies
there. Noncommutativity of an almost-simple group ensures that its identity
and trivial maps differ.

The actual closed retract image is smooth and has geometrically connected
fibres. The unit-étale loci of the image inclusion and its unit inclusion
therefore give actual identity and triviality on opens. The residue
dichotomy makes those opens cover, and nontriviality makes them disjoint.
Thus this proof retains arbitrary nonreduced bases: it does not infer global
equality merely from equality on geometric fibres.

This internally derived construction supplies the geometric part of the
relative normal-idempotent statement. It does not yet turn the clopen subset
of an affine base into a ring idempotent or translate a transformation of
restricted affine point functors into an actual group-scheme map.
