# Whole smooth-dual gamma factors on actual block shapes

This internal unit composes the Library's natural normalized induction duality,
finite tensor duality and gamma invariance under equivalence with
`BlockShapeCenteredGamma`. It retains the supplied actions, the original block
shape and ordering, and the standard upper normalized induction.

`HasNormalizedProductSmoothDualEquivalence T B π` states that the actual smooth
contragredient of the normalized product of `π i` is equivalent to the normalized
product of the actual smooth contragredients of `π i`, using the same topology
`T`. Its proof `hasNormalizedProductSmoothDualEquivalence` assumes admissibility
of every block. The external finite tensor is admissible. Natural normalized
induction duality identifies the whole smooth dual with the induction of the
Levi smooth dual. The canonical tensor map from the external tensor of the block
smooth duals to the Levi smooth dual is injective by finite tensor dual
injectivity and surjective by admissibility and compact-open cofinality.
Inducing its inverse gives the claimed equivalence.
`normalizedProductSmoothDualEquiv` chooses this equivalence.

These declarations have independent field and block-carrier universe levels.
They allow every block shape, including the empty shape at ambient rank zero;
they impose no additional irreducibility, unitarity or genericity hypotheses.

`IsPadicSymmetricGammaFactor.normalizedProduct_smoothDual` starts with a supplied
equivalence from an original action to a normalized product and a gamma
certificate pairing that action with its actual whole smooth dual. Contravariant
smooth-dual transport and the preceding product equivalence identify the second
action with the product of block smooth duals. Gamma invariance under the two
equivalences gives precisely the mixed-product certificate used by the centered
block construction.

`centeredSegmentFamilyGammaGerm_of_smoothDualGamma` uses this transport for the
determinant-twisted square-integrable blocks. Admissibility of each untwisted block
implies admissibility of its twist. The original action's standard functional
transports to the whole induction, and the existing block-shape germ theorem
then gives the centered gamma germ with its existential nonzero epsilon
coefficient and integral exponent.

`unitarySupercuspidalProduct_of_smoothDualGamma` similarly supplies the
mixed-product gamma certificate to the existing centered rigidity theorem.
Square-integrability supplies admissibility of the untwisted blocks. With
the supplied real-order restriction, that theorem concludes that the original
action is a normalized product of unitarizable supercuspidal representations on
the same block shape. The output block-carrier universe is independent of both
the original action and the classification blocks.

The provenance is internal extraction and composition of imported Library
proofs, using the same tensor-duality route as `twistedProductOrdinaryDual`
without rewriting the block smooth duals as twists of untwisted duals.
The segment-head and equal-rank factor statements, supplied segment parameters,
unitary generic data, actual whole smooth-dual gamma certificate and real-order
restriction remain premises of the rigidity conclusion. This unit does not
prove classification exhaustion, construct arbitrary segment parameters,
establish the global associated-pair gamma comparison or discharge the global
associated supercuspidal induction statement.
