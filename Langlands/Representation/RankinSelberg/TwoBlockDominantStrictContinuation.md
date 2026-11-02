# Strict coefficient continuation and intrinsic denominator bounds

This module gives internal consequences of the published unequal-rank analytic
theorem and determinant-slice expansion. It does not translate a new assertion
from the literature. The canonical p-adic topology, the supplied scalar Haar
measure, the supplied compatible unipotent quotient measure, and independent
field and representation universes are retained.

`strictRectangleMeasure` was defined in `TwoBlockDominantStrictCoefficients` by
transporting the actual finite product of the supplied scalar Haar measure from
the finite-function measurable structure to its equal Borel structure. The
private property-transport lemma eliminates an equality of measurable spaces.
It transports a property of the measure, without taking a pushforward or
changing any measure mass. `strictRectangleMeasure_sigmaFinite` applies this
lemma to sigma-finiteness; the original product measure is sigma-finite because
the canonical field is sigma compact.

The elementary private integral-transport proof follows the equality-elimination
helper in Workers 113 and 1209's `TwoBlockDominantFirstBlockLaurentIdentityProof`;
their contribution is credited with this unit. The present property transport
and its applications to analysis, sigma-finiteness and intrinsic generators
are the new assembly.

`strictRankAnalyticAt` substitutes the equality specifying the larger rank,
applies `unequalRankAnalytic` with the original product measure, then transports
the entire analytic conclusion through that same measurable-space equality.
Full Whittaker type and nonzero functionals are its explicit hypotheses.
Compatibility of the supplied quotient measure and right invariance of the
fixed unipotent Haar measure remain explicit. The conclusion concerns the exact
Borel rectangle used by `strictSliceCoefficient`.

`strictIntegral_eq` proves that the resulting Borel rectangle integral equals
the original `unequalRankIntegralAt`. The proof is pointwise in the spectral
parameter and quotient variable, and reduces equality of the inner integrals
to elimination of the measurable-space equality. It makes no convergence
claim and uses no Fubini interchange.

`strictCoefficient_continuationData` extracts actual product-space convergence
and rational continuation from the transported analytic conclusion.
`unequalRank_hasBilateralSpectralExpansion` turns that convergence into the
spectral expansion of the actual coefficient series. The exact integral
equality then identifies both the expansion and continuation with the original
supplied product-Haar integral.

`strictCoefficient_polynomialDivisibility` starts with uniform finite clearing
of every pair of coefficients in the two fixed nonzero models. It transports
the intrinsic normalized-generator hypothesis from the original product
measure to the Borel presentation. The existing
`strictModelFiniteClearing_polynomialDivisibility` then gives polynomials
`Q` and a natural number `e` with `X ^ e * A = Q * P`. This is the intrinsic
denominator direction required by the dominant-rank task. There is no new
factor-existence or analytic premise beyond the hypotheses shown in Lean.
