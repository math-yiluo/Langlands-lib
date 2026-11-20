# Local vanishing and support descent for smooth distributions

Multiplication by a fixed smooth scalar function defines a continuous
linear map of a smooth test space to itself. The product is supported
in the original support. Mathlib's continuous multiplication on a
fixed compact support gives the continuous map on all tests.

In a finite-dimensional real normed space, a distribution vanishing
on each member of a family of opens also vanishes on their union.
For a test supported in the union, choose a smooth partition of unity
subordinate to the family on its compact support. Only finitely many
of those functions are nonzero on the support. Multiplying the test
by these functions splits it into a finite sum of tests supported in
the individual opens. Each summand has zero evaluation.

The complement of distributional support is the union of the opens
where the distribution vanishes. Consequently the distribution
vanishes on that open complement, and empty support implies the
distribution is zero. To shrink a proposed support from \(S\) to
\(T\), it is enough to find an open neighborhood of vanishing at
each point of \(S\setminus T\). Iterating this implication along a
finite filtration whose last term is empty gives global vanishing.

These internal results supply the local-to-global step for support
descent along matrix strata.
