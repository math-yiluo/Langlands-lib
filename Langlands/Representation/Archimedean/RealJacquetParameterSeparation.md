# Infinitesimal-character separation for real Jacquet functionals

This internal lemma applies `GelfandParameterSeparation` to the real standard
module. A nonzero Jacquet functional kills the strictly upper triangular matrix
units and is an eigenfunctional for each diagonal matrix unit. Applying
`ComplexJacquetFinite.diag_pow` modulo its kernel evaluates the diagonal of each
Gelfand matrix power by the shifted recursion. The trace is scalar because it
comes from the central element in `RealJacquetFiniteGenerationProof`. Two
nonzero functionals of the same module therefore give the same sums, so their
shifted parameter multisets agree.

In the normalized real principal series, evaluation at the identity has the
Jacquet exponents and signs of the inducing characters. Its diagonal
calculation uses the derivative of left equivariance on positive diagonal
matrices, and its sign calculation uses the diagonal sign reflections. Applying
the separation result to this evaluation and a second nonzero Jacquet
functional gives the parameter multiset in normalized induction coordinates.
The compact sign monomial extends by principal-series extension and takes
the value one at identity, so the evaluation functional is nonzero.

The compact restriction of a standard-module vector is determined by
evaluations at identity of its compact translates. The uniqueness of
principal-series extension then detects the vector from these evaluations.
