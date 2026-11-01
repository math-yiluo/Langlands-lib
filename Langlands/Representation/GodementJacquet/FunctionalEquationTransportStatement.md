# Representation-equivalence transport of normalized matrix equation data

`Langlands.GodementJacquet.NormalizedMatrixFunctionalEquationTransportStatement`
is an internal transport statement derived from the published definitions in
[`AnalyticData`](AnalyticData.md). Its provenance is invariance of the actual
bi-smooth coefficient submodule under a representation equivalence, as proved
in [`CoefficientTransport`](CoefficientTransport.md). It does not introduce a
new analytic existence assertion or translate an additional literature theorem.
This file defines the proposition; it supplies no proof.

For a field `F : Type uF` with the supplied topology and measurable structure,
the statement quantifies over every rank `n + 1`,
including rank one. It retains the supplied measurable structure on
`GeneralLinear (n + 1) F`. The two complex representations have carriers
`V : Type uV` and `W : Type uW` with independent universes. An actual
`Representation.Equiv` between those actions implies equivalence of their
`NormalizedMatrixFunctionalEquationData` predicates.

All other arguments are identical on both sides: the natural number `q`, unitary
additive character `ψ`, scalar additive Haar measure `ν`, absolute value `abv`,
group measure `μ`, polynomials `P` and `PDual`, complex unit `c`, and integer
`m`. No field-locality, smoothness, admissibility, irreducibility,
character-nontriviality or self-duality assumption is needed for this transport
claim. The predicate still contains the same ordinary and inverse-transpose
analytic assertions, including common right convergence half-planes, actual
rational continuation for each test and coefficient, and normalized generator
equalities with constant coefficient one.

In the Fourier clause, each full-matrix Schwartz test `Φ` has one Schwartz
witness `ΦHat` before the universal coefficient quantifier. The Fourier pair
uses the plus transpose pairing and precisely the square product of `ν`.
The coefficient on the transformed side remains the original function
precomposed with inverse transpose. The equation quantifies over every actual
continuation pair and retains both denominator guards, the original normalized
shift, the variable `q^(-s)`, central scalar `1` and sign exponent `0`.
These clauses are preserved by reusing the unchanged data predicate, rather
than by replacing its coefficient family with a model or contragredient.

Specializing the quantified arguments gives the canonical p-adic transport
interface: use the field's canonical topology, Borel structures, residue
cardinality, normalized absolute value and group Haar measure, while retaining
the supplied scalar measure. This observation is a specialization of the
statement, not an existence result for any of those data.
