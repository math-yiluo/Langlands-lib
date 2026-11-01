# Uniform Laurent clearing through entire parameters

Worker 486. Internal support for extending an actual polynomial-cleared
coefficient family from sufficiently large real parameters. This uses the
published bilateral Laurent-series module and the companion entire
coefficient identity theorem.

`UniformlyFiniteCoefficientSupport c` requires one finite set of integer
exponents containing the support of `c(u,_)` for every complex parameter.
If an entire coefficient family has finite support at uncountably many
parameters, countably many candidate finite sets cover those parameters.
One candidate works on an uncountable subset. Every coefficient outside
that finite set vanishes on an uncountable set and therefore vanishes
identically by the published scalar identity theorem. In particular,
pointwise finite support on a sufficiently large real ray gives one
common finite support on the whole complex parameter plane. A common
degree bound on the pointwise cleared outputs is not assumed.

For a Laurent-polynomial kernel whose support lies in one fixed finite
set, padding its coefficient sum with zero terms identifies the actual
published Laurent action on bilateral series with the companion finite
convolution. Analytic kernel coefficients and an entire series family
therefore make the actual cleared series entire coefficientwise.

`laurent_clearing_of_real_gt` assumes that the actual cleared bilateral
series is the coefficient series of some Laurent polynomial at every
sufficiently large positive real parameter. The polynomial may depend
arbitrarily on that parameter. The common-support argument constructs an
actual Laurent polynomial at every complex parameter with exactly the
cleared coefficients. Its coefficients are entire and one finite set
supports the whole resulting polynomial family.

This is an internal combination of countability, the existing analytic
identity theorem and the actual bilateral coefficient embedding. It does
not construct the initial Whittaker family, prove determinant-slice
analyticity, supply a clearing kernel, or identify convergent bilateral
spectral sums with rational continuations. In particular the rational
denominator bound above a model twist threshold still needs that last
coefficient bridge before it supplies the present real-ray hypothesis.
Neither closed adjacent-rank parent target is proved here.
