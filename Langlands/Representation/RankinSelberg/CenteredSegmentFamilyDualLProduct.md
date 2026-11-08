# The dual Appendix L-product and its gamma expression

Author: Worker 1765.

This internal adapter records the simultaneous equality of the original and
actual smooth-dual spectral reciprocals with one Appendix `blockLFactor`.
The segment-head and equal-rank supercuspidal factor formulas, the pair
certificates and their exact polynomial products remain explicit premises.
The bidual wrapper also retains admissibility of the original blocks.

The explicit midpoint-base Euler data are independent of the additive character
and self-dual measure: their finite unramified twist parameter sets use the
actual actions, while character and measure enter only their certificates.
`centeredSegmentBaseEulerFamily_data_character_independent` proves this by
eliminating the equality of independently supplied ranks in the equal-rank
branch and unfolding the empty-data constructor in the unequal-rank branch.
It does not assert general character independence
of all Rankin–Selberg factor relations.

For a reversed pair, symmetry of `IsPadicRankLPolynomial` exchanges its two
actual actions. Transposing the two finite product indices then gives precisely
the ordinary mixed-family product. The Euler-data equality identifies its base
functions for the two supplied characters and measures. In particular the second
character can be the inverse character used by the dual functional equation.

For the actual dual of the mixed pair, the second member is the smooth bidual
of a real-twisted original block. Open-kernel twisting preserves its supplied
admissibility. Cofinality of compact open subgroups gives the canonical
bidual equivalence, which preserves the pair-polynomial certificate. The
reverse-pair result then applies. This retains the actual dual actions rather
than substituting a representative of their isomorphism classes.

`IsCenteredSegmentFamilyLProductPair` is a conjunction of the two pointwise
L-product identities. The assembly theorem supplies it from the original and
dual pair certificates. Its `gammaExpression` theorem substitutes those
identities into epsilon times the reflected dual reciprocal divided by the
original reciprocal, giving the Appendix `blockGamma` as an equality of complex
functions. Complex inverse is totalized, including at polynomial zeros.
No equality between this expression and rational gamma evaluation at poles,
no meromorphic-order conclusion and no proof of the retained factor formulas
is asserted by this unit.
