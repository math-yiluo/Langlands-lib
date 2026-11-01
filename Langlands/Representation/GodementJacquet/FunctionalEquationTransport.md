# Transport of full normalized matrix functional-equation data

This module proves the internal
[`NormalizedMatrixFunctionalEquationTransportStatement`](FunctionalEquationTransportStatement.md).
It imports the existing actual-data transport theorem from
[`RankOneMatrixFunctionalEquationComparisonTransport`](../RankinSelberg/RankOneMatrixFunctionalEquationComparisonTransport.md).
No additional literature theorem or analytic existence input is used.

`normalizedMatrixFunctionalEquationTransport` introduces the universally
quantified arguments of the closed statement and directly applies the published
`GodementJacquet.normalizedMatrixFunctionalEquationData_equiv`. That theorem
handles equivalent complex representations on independently universed carriers
over a field with the supplied topological and measurable structures. Its
existing proof unfolds the outer data conjunction, applies the ordinary and
transformed analytic transport equivalences, and rewrites the actual coefficient
submodule in the Fourier clause. This module reuses that proof.

The imported theorem preserves every function, rather than choosing a representative
coefficient on a new model. The same Schwartz Fourier witness remains available
for each test before quantifying over all coefficients. Its plus transpose
pairing and supplied scalar product measure remain unchanged. The transformed
coefficient is still the function precomposed with inverse transpose.
Both analytic branches keep their common convergence bounds, rational
continuations and normalized generator properties. The fixed values of `q`,
`ψ`, `ν`, `abv`, `μ`, `P`, `PDual`, `c` and `m` are the same on both sides.
Every continuation pair remains universally quantified, retaining the
normalized shifts, `q^(-s)` and both denominator guards in the normalized
equation, with central scalar `1` and sign exponent `0`.

`Padic.normalizedMatrixFunctionalEquationData_equiv` specializes the same theorem
to the canonical p-adic topology, Borel structures, residue cardinality,
normalized absolute value and general-linear Haar measure. It retains the
supplied scalar additive Haar measure exactly.

This is a conditional transport result for every rank `n + 1`, including rank
one. It assumes an actual equivalence of the representations and establishes
equivalence of their proposed data. It constructs no analytic data and uses no
smoothness, admissibility, irreducibility, nontrivial-character or self-duality
hypothesis.
