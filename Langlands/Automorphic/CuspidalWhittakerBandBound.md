# Actual band integrability and the Whittaker derivative-bound predicate

`CuspidalWhittakerBandBound` is a proposition about the actual cusp Whittaker
coefficients, actual enveloping action and canonical determinant-band quotient
Haar L² norm. For each compact open finite subgroup J and compact set Q of
adelic group points, it requires a finite set of enveloping operators D and a
nonnegative real constant C. These choices precede the original J-fixed vector
and the group point. The bound is C times the sum of the band norms of the
D-derivatives of that original vector. There is no requirement that each
derivative be J-fixed.

The integrability witness supplied to the predicate is for the actual cusp
functions, descended to the rational quotient and restricted to
`1 < |det| < 2`, with `OperatorDeterminantSlice.quotientHaarMeasure`.
`memLp_cuspidal_toQuotient_band` constructs this witness using the published
cuspidal band cover and `memLp_band_of_cover`. It assumes neither a replacement
positive form nor a norm on an abstract isomorphic representation.

The module defines the bound predicate and proves actual band integrability;
it does not prove the bound. A separate Sobolev application can supply the
predicate after its compact Sobolev premise is established. The actual norm,
derivatives and quantifier order remain explicit here.

This is an internal definition and integrability consequence of published
cuspidal band-cover results. The module constructs no smooth Hilbert
globalization, extension of equivalences or functionals, or local or global
Whittaker uniqueness. Its use in the band reduction retains the estimate
and analytic comparison as open premises.
