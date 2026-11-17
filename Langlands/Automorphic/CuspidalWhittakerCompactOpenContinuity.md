# Compact-open continuity of actual cuspidal Whittaker coefficients

Worker 805. This internal analytic prerequisite concerns the actual functions of
`CuspidalOperatorRealization F r`, for arbitrary number-field universe and every
rank `r + 1`. It is not a multiplicity-one theorem.

`functionMap` retains the original continuous function with the compact-open
topology. The realization space inherits its topology through the subspaces of
stable automorphic functions, finite smooth functions and continuous rational
functions. Thus this map is continuous without an extra hypothesis.

`continuous_family` proves that a compact-open continuous family of actual
vectors has Whittaker coefficients jointly continuous in the family parameter
and group point. The integrand descends to the compact rational unipotent
quotient. Joint evaluation on the locally compact adelic matrix group is
continuous; multiplying by the continuous generic character preserves
continuity. The open quotient map descends this continuity, and compact
integration gives the result. Specializing to the identity family proves
`continuous_coefficient` and the entry proposition
`CuspidalWhittakerCompactOpenContinuityStatement`. `continuous_at_point` fixes the
group point, and `functionalCLM` bundles the
already published linear functional at a fixed point with this continuity.

This is an internal consequence of the published actual-function realization,
normalized rational unipotent quotient integral, local compactness and compact
parametric integration. No external theorem or new source identification is
asserted. The argument extends the fixed-vector continuity argument of
`Langlands.Global.RankinSelbergGlobal.Unfolding.continuous_cuspWhittaker'` to a
varying realized vector.

The topology here is inherited compact-open function topology. No continuous
inclusion from a Hilbert smooth-vector space, finite derivative-norm bound,
continuous extension of an arbitrary operator equivalence, smooth globalization
or uniqueness of Whittaker functionals is proved. Those bridges remain needed
for `CuspidalOperatorMultiplicityOneStatement`.
