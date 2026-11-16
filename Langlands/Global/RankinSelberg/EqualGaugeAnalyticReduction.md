# The equal-rank gauge premises from one analytic estimate

This internal composition states and proves
`EqualGaugeAnalyticReductionStatement.{u}`:
`WhittakerSchwartzGaugeStatement.{u}` implies the unchanged
`EqualUnfoldingGaugeStatement.{u}`. The analytic statement remains a hypothesis.
This module proves neither that estimate nor the unconditional gauge statement.

The implemented proof has two components, corresponding exactly to the
conjunction in the target. For the primal component, `equalGaugeSpecialization`
applies the analytic estimate to actual cusp functions and yields
`EqualWhittakerSchwartzStatement`. Then `equalGaugeReduction` uses the
second cusp function's central power bound and the quotient integration
identity to obtain the primal gauge premise for every equal-rank pair.

For the dual component, `equalGaugeDualSpecialization` applies the same
analytic estimate to the transpose-inverse cusp space. Its proof uses the
inverse standard additive character, the dual Whittaker identity, the dual
central bound, Fourier stability, and quotient integration. It yields the
dual gauge premise for every equal-rank pair.

The ordered pair of these universal conclusions is exactly the existing
`EqualUnfoldingGaugeStatement`; no target or imported definition is changed.
Both components retain all number fields `F : Type u`, their field and
number-field instances, compactness of `AdeleQuotient F`, every rank `r + 1`,
and every pair of actual cuspidal realizations. The uniform thresholds and
the measures are those of the respective existing gauge predicates.

The provenance is internal composition of the explicitly named conditional
specializations and reduction. No additional external-source claim or
unconditional convergence claim is made.
