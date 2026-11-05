# Continuous parabolic vanishing in the actual positive quotient L²

This internal adapter connects `GroupSchemeParabolicCuspidal` to
`GroupSchemeQuotientL2`, preserving both existing carriers. The parameters
are an arbitrary number field, the actual affine connected reductive group
`G`, the supplied commutative group scheme `T` and morphism `i : T → G`,
the explicit `ParabolicDynamicStatement`, and supplied measures on the
canonical all-proper-parabolic radical quotients.

`positiveParabolicCuspidalSubrepresentation` pulls the continuous
all-parabolic vanishing condition back along the existing injective map
`positiveQuotientContinuousPullback`. Its carrier consists of continuous
functions on the actual positive-central rational quotient whose actual
adelic pullbacks belong to `parabolicCuspidalSubrepresentation`. The
existing pullback intertwining law proves stability under positive right
translation. Convergence remains part of the underlying vanishing
condition; the finite Borel specialization is supplied by the preceding
module.

For a measure `measureQ` on that actual quotient and the explicit
`QuotientMeasureRightInvariant` hypothesis,
`positiveParabolicCuspidalL2Subrepresentation` intersects this space with
the existing continuous `MemLp` subspace at exponent two. Square
integrability is thus an explicit restriction, not an assertion about
every continuous vanishing function.

`positiveParabolicCuspidalL2ToLp` is the original complex-linear
`continuousL2ToLp` after forgetting the vanishing condition. It is an
intertwining map into the actual `Lp ℂ 2 measureQ`, with the original
positive right action. Its representative agrees almost everywhere with
the continuous function. If the measure is positive on nonempty open
sets, the map is injective: equality of its classes gives equality of the
original continuous square-integrable representatives by the preceding
module's full-support result, then equality of their subtypes.

`continuousParabolicCuspidalL2Image` is precisely this map's algebraic
image, as a subrepresentation of the actual quotient L² representation.
The membership theorem supplies exactly a continuous square-integrable
vanishing representative.

The canonical specialization uses exactly
`positiveRationalQuotientHaarMeasure`, with the previous character
restriction injectivity, finite-index image, finite split-torus
isomorphism, centrality, local-finite-type and norm-one right-Haar
invariance hypotheses. The existing normalization and full-support proof
give faithfulness for this measure. No rescaling or new measure choice is
introduced.

All constructions and proofs are compositions or intersections of the
named preceding objects. This unit does not identify the supplied `T`
with the greatest rational split central torus, normalize the supplied
radical measures, prove automatic cuspidal square integrability, impose
all automorphic finiteness conditions, or prove closedness, density, finite
volume or general-linear comparison. In particular, its algebraic image
is not asserted to equal the full almost-everywhere cuspidal subspace of
Getz–Hahn (6.20)–(6.21).
