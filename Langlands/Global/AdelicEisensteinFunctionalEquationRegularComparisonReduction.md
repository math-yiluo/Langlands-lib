# Reduction of the Eisenstein functional equation to regular-patch comparison

`Langlands.Global.eisensteinFunctionalEquationRegularComparisonReduction`
proves `EisensteinFunctionalEquationRegularComparisonReductionStatement`.
The exact published functional equation follows from
`EisensteinFunctionalEquationRegularComparisonStatement`.

For each summand choose the agreement bound `R i` of its supplied `Q`-series
continuation. The sum of the nonnegative parts `max (R i) 0` bounds each of
these real numbers, including when some are negative. Request a comparison
patch at that bound. The regularity inequalities there imply the individual
ones, so each convergent `Q`-series may be replaced by its continuation.
The resulting equality on the patch extends by
`eisensteinFunctionalEquation_of_openAgreement` to the requested domain
for every adelic point. The bound and finite sum are also defined for the
empty family.

The proof implements scalar continuation after the initial comparison in
Bernstein–Lapid §8.6. The comparison itself is the premise of the proved
implication.
