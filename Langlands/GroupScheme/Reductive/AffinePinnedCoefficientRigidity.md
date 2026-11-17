# Detecting pinning coefficients on local tests

This internal helper fixes an actual automorphism of an affine pinned model.
Assume its pullback along the identity of the base preserves the concrete
local pinning. If its actual differential carries one original chosen simple
vector to a scalar multiple of another, that scalar is one.

The construction `pinningCoefficient` first projects the image of a chosen
source vector to the actual exponent weight space of the target simple root,
then extracts its coefficient using the supplied target-line trivialization.
It is defined for every original automorphism and pair of simple roots.
For a supplied scalar-multiple image equation, the projection formula proves
that this coefficient is exactly the specified scalar.

On every local coefficient algebra, the local pinning predicate gives a
permutation of the original simple vectors. Projection from the identity
pullback converts the pinning-point equation into an equality for the actual
coefficient-extended differential. Naturality of the Lie target map extends the
supplied scalar equation to that algebra. The published simple-vector scalar
rigidity theorem then forces the image of the scalar to be one.

Apply this to the localizations at all maximal ideals of the original ring.
Mathlib's localization detection theorem gives that the original scalar equals
one. The resulting exact chosen-vector equation is recorded as a second lemma.
The ring may be nonreduced or zero; no field or connectedness hypothesis is
required. This is a consequence of the published all-test pinning-vector
rigidity and coefficient naturality, not an existence theorem for pinned
representatives.
