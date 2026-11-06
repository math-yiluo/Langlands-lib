# Proof of actual quotient-period representative congruence

The exact theorem `Langlands.QuotientIntegration.quotientPeriodAEEq` proves
`QuotientPeriodAEEqStatement` without changing its hypotheses.

The exported helper `ae_lift_discreteQuotientMeasure` uses the actual Borel
fundamental domain and subgroup countability. Every subgroup translate is a
fundamental domain with the same quotient pushforward. Pulling back an
almost-everywhere quotient assertion therefore proves it on every restricted
translate. The countable sum of these restrictions equals the ambient measure,
which proves the assertion almost everywhere on the entire group.

For each period-group element, left Haar invariance transfers the lifted
representative equality under the actual left multiplication. The composed
quotient functions are measurable on the product. Almost-everywhere Fubini
therefore gives equality on the canonical period domain for almost every
ambient element. The actual quotient pushforward and its inverse-mass scaling
carry that equality to the normalized period quotient. Multiplying by the
same descended inverse character gives equality of the actual integrands.
Integrability congruence compares absolute convergence, and Bochner integral
congruence compares the periods, even in cases where neither converges.

This implementation does not invoke a convergence theorem or assume finite
positive domain mass, compact period quotient, period-measure invariance,
L2 membership, normality or character unitarity. It keeps specified functions
throughout and supports a later justified Lp representative comparison.
