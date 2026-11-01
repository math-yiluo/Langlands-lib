# Top Euler coefficients and strict support bounds

`EulerCoefficientDetectsSupport` is an internal predicate for the actual
coherent Euler polynomial at truncation `d`. It asserts that coefficient `d`
is nonnegative, and that this coefficient is positive exactly when the
coefficient sheaf fails `HasSupportDimensionLT M d`. The definition does not
assert that the criterion holds.

The helper results concern proper schemes over a field, in arbitrary universe
`u`, with the Noetherian and separated hypotheses used by coherent Euler
polynomial reconstruction.

If `M` has support dimension strictly less than `d`, its coefficient at `d`
vanishes. For `d = 0` the support bound makes the sheaf zero. For `d + 1`,
truncation independence identifies the polynomial with its truncation at `d`,
whose degree is at most `d`.

For support dimension at most zero, the constant coefficient is the actual
Euler characteristic. The published finite-support positivity theorem says
that it is positive exactly for a nonzero sheaf. A zero sheaf has zero Euler
polynomial, giving nonnegativity in the remaining case. The support bound
strictly below zero is equivalent to being a zero object. This proves
`eulerCoefficientDetectsSupport_zero`.

On an integral scheme, a nonzero coherent ideal sheaf has the same coefficient
as the structure module at every finite ambient dimension upper bound `d`.
The ideal inclusion gives an actual short exact cokernel sequence, so coherent
Euler polynomial additivity applies. The published ideal-open theorem bounds
the cokernel support strictly below `d`. Its coefficient at `d` therefore
vanishes by the first helper, leaving the asserted equality. This includes
dimension zero.

These are internal consequences of coherent Euler reconstruction, finite-support
positivity, additivity and the nonempty unit locus of a nonzero integral ideal.
They do not prove the ample coefficient criterion in positive dimension.
