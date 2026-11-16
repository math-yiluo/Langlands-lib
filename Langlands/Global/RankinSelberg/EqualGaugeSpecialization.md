# The analytic gauge estimate on actual cusp functions

This internal conditional result specializes
`WhittakerSchwartzGaugeStatement` to the cusp functions of every actual
cuspidal operator realization. It proves
`EqualGaugeSpecializationStatement`: the general analytic estimate implies
`EqualWhittakerSchwartzStatement`. The analytic estimate remains a premise.

The field is any number field `F : Type u` with compact `AdeleQuotient F`.
The rank is `r + 1`, and the realization is the existing
`CuspidalOperatorRealization F r`. No hypothesis is added to that realization.
The conclusion has one nonnegative convergence threshold for each realization,
uniform over standard additive characters, vectors, Schwartz–Bruhat functions,
and real exponents above the threshold.

The implemented proof uses the published function space `cuspSpace F T`,
the derivative family `cuspDerivative F T`, and the theorem
`whittakerDecayClass_cuspSpace`. The theorem
`CuspCentralBound.exists_norm_cuspFunction_le` supplies a single real exponent
for all vectors of `T`, with a separate nonnegative constant for each vector.
Transport through `cuspEquiv F T` proves
`EqualGaugeSpecialization.hasCentralPowerBound_cuspSpace`, so this space
satisfies both hypotheses of the general analytic estimate.

The helper
`EqualGaugeSpecialization.equalWhittakerSchwartzBound_of_cuspSpace`
evaluates that estimate at `cuspEquiv F T v`. Its underlying function is
definitionally `cuspFunction F T v`, and its Whittaker function is
definitionally `cuspWhittaker F T ψ v`. The integrand, last-row map,
determinant weight, and measure `whittakerQuotientMeasure` consequently
agree with `EqualWhittakerSchwartzBound`, without changing the threshold.
The theorem `equalGaugeSpecialization` performs these two steps for every
field and realization, retaining universe `u`.

The provenance is an internal consequence of the named Library constructions
and the explicit analytic premise. This module proves neither the premise nor
the unconditional `EqualUnfoldingGaugeStatement`.
