# Applying a general Whittaker–Schwartz estimate to the dual cusp space

This internal conditional result specializes
`WhittakerSchwartzGaugeStatement.{u}` to the dual half of the equal-rank
unfolding gauge proposition. `EqualGaugeDualSpecializationStatement.{u}` says
that the general estimate implies `DualEqualWhittakerGaugeIntegrable F T T'`
for every number field `F : Type u` with compact additive Adele quotient,
every `r : ℕ` and every pair of actual cuspidal realizations of rank `r + 1`.
The theorem `equalGaugeDualSpecialization` proves this implication.
The general weighted estimate remains an explicit hypothesis.

The helper `exists_norm_iotaCuspSpace_le` uses the two linear equivalences from
vectors to cusp functions and then to their transpose-inverse functions. Every
function of `iotaSpace F (cuspSpace F T)` is therefore a dual cusp function.
`CuspCentralBound.exists_norm_dualCuspFunction_le` supplies one exponent for the
whole space, with a nonnegative constant for each element.

The helper `dualEqualWhittakerSchwartzBound_of_iotaSpace` applies the uniform
weighted Whittaker–Schwartz bound on this space at the inverse standard additive
character. The published identity `dualCuspWhittaker_eq_whittaker` identifies its
Whittaker function with the dual Whittaker function of the original vector.
The standardness of the inverse character and the two linear equivalences
preserve all uniformity in the threshold. Its conclusion is the weighted
dual bound on the same `WhittakerQuotient` with the same
`whittakerQuotientMeasure`.

The theorem `dualEqualWhittakerSchwartzBound` supplies the two hypotheses of
the general estimate for the transpose-inverse cusp space. The published
`whittakerDecayClass_cuspSpace` and `whittakerDecayClass_iotaSpace` give its
decay class, using the transported derivative `iotaDerivative`. The first
helper above gives `HasCentralPowerBound`. Applying the general estimate
and then the Whittaker identification proves
`DualEqualWhittakerSchwartzBound F T`.

Finally, `dualEqualWhittakerGaugeIntegrable` applies the conditional reduction
in `EqualGaugeDualReduction`. That reduction absorbs the second dual cusp
factor using its realization-dependent central exponent, applies Fourier
stability to the test function, and transports the finite majorant integral
to the rational unipotent quotient. It yields precisely the existing dual
gauge predicate, uniformly in standard additive characters, both vectors
and Schwartz–Bruhat functions. Universally quantifying this result proves
`equalGaugeDualSpecialization`.

The provenance is internal: the argument composes the Library's cusp-space
equivalences, central bound, dual Whittaker identity, decay-class transport
and dual gauge reduction with the explicitly assumed general analytic
statement. It does not construct a contragredient cuspidal realization.
This module proves neither the general analytic statement nor the
unconditional `EqualUnfoldingGaugeStatement`.
