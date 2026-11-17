# Conditional assembly of the rectangular Whittaker gauge bound

`unequalRectGauge_of_simpleRootGauge` proves the unchanged Library proposition
`UnequalRectGaugeStatement.{u}` under two explicit analytic premises:
`WhittakerSimpleRootMajorizationStatement.{u}` and
`AdelicSimpleRootGaugeRectangularMellinStatement.{u}`.
Both analytic conclusions remain unproved. The statement, gauge and
translated-dual bridge interfaces are independently reviewed Library results.

The implemented proof applies
`translatedDualCuspWhittaker_majorization_of_simpleRoot` to the given number
field and actual cuspidal realization. This supplies common exponents `β` and
`τ ≥ 0` and the required pointwise majorant for every standard character and
vector. It then applies
`rectWhittakerGaugeBound_of_simpleRootGauge`, which absorbs the determinant
power by shifting the Mellin exponent and uses the rectangular convergence
premise.

All number-field hypotheses, the compactness of `AdeleQuotient F`, arbitrary
universe `u`, and every `t < r` are retained. This internal composition verifies
that the two analytic interfaces suffice for the exact target; it does not
discharge either premise or claim an unconditional proof of the target.
