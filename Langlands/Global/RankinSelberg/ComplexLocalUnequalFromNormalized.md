# Reduction to the normalized complex unequal-rank equation

The value of each Whittaker intertwiner at a vector belongs to its
range and hence to the corresponding complex Whittaker model. Applying
`complexLocalUnequalConvergence` to these model elements proves
`ComplexUnequalIntertwinerConvergenceStatement` for the exact ordinary
and dual kernels on a shared right half-plane.

`complexLocalUnequalFromNormalized` then applies
`complexUnequalAnalyticReduction` to this convergence theorem. The
remaining premise is `ComplexUnequalNormalizedIntertwinerEquationStatement`,
which asks for entire normalized continuations of the two integrals on
intertwiner values and the normalized functional equation. The
conclusion is the full Library proposition on the two Whittaker models.

This is an internal reduction of Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), Theorem 2.1 (i)–(iii) in the complex unequal-rank case.
