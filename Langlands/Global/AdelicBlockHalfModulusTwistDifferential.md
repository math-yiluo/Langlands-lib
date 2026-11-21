# The Lie shift of an inverse half-modulus block twist

For a curve in one invertible Levi block, the ambient parabolic curve
has derivative in that block alone. Thus only one trace contributes
to the differential of the half-character. The selected block's Hecke
twist is the reciprocal of this half-character. Differentiating at
the identity gives the negative outer exponent times the block trace
at a real place, and the negative outer exponent times twice the real
part of the trace at a complex place.

The curve `GeneralLinear.matrixExponentialCurve X` has value one
and tangent \(X\) at zero. Its inverse at parameter \(t\) is the
exponential with parameter \(-t\). Inserting the curve at one place
gives the inserted tangent in archimedean coordinates. The chain
rule for the determinant character in the units chart identifies
the scalar derivative with `characterDifferential`, which enters
the enveloping shift of the Hecke twist.

On an actual operator realization the Hecke twist equivalence
then carries the original Lie action minus this outer trace
contribution to the twisted Lie action. It also intertwines
compact actions at both kinds of place. The latter follows
from the value one of the twist on the compact Levi block.

The scalar identities use `AdelicBlockHalfModulusTwistPlace` and
`AdelicBlockParabolicPlaceDifferential`.
