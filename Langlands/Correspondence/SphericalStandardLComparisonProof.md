# The standard L-polynomial of every spherical class

Worker 1737 supplies the final composition and this explanation. Workers 1761,
1697, 1650 and 706 supplied the spherical standard-module proofs; Workers 1789
and 1738 supplied the ordered principal-series polynomial proof.

`Langlands.Correspondence.sphericalStandardLComparison` proves the unchanged
[`SphericalStandardLComparisonStatement.{uF, uA} F`](SphericalStandardLComparisonStatement.md).
The field universe `uF` and automorphic carrier universe `uA` remain independent.
For every prime and p-adic field, every nontrivial additive character and
self-dual Haar measure, every positive rank, spherical class with supplied
spectrum `s`, trivial rank-one class, and supplied Langlands pair-polynomial
certificate `P`, the conclusion is
`P = Unramified.Eigenvalues.eulerPolynomial s`. The hypotheses are exactly
those of the published statement.

The Lean proof applies
[`sphericalStandardLComparison_of_prerequisites`](SphericalStandardLPrerequisites.md)
to the two published unconditional theorems
[`sphericalTemperedStandardModule.{uF, uA} F`](SphericalTemperedStandardModuleProof.md)
and
[`orderedUnramifiedPrincipalSeriesLPolynomial.{uF} F`](OrderedUnramifiedPrincipalSeriesLPolynomialProof.md).
These discharge both premises of the conditional comparison.

The conditional comparison unpacks the class certificate into actual
equivalent representatives and transports the supplied spherical spectrum to
the irreducible admissible representative. The first theorem supplies a
tempered Langlands quotient datum `d` and a tuple `z` with spectrum exactly
`s`, weakly increasing norms, and an actual equivalence between the standard
module of `d` and the normalized upper-Borel principal series of `z`.
The trivial rank-one class and the existing rank-one standard-module
equivalence identify the second standard module with the actual trivial
character representation. The pair certificate applies to every presenting
datum pair, hence to these chosen data. Transport along the actual
representation equivalences gives the supplied JPSS polynomial certificate
for that ordered principal series against the trivial character.

The second theorem computes this certificate as the Euler polynomial of
`Eigenvalues.ofTuple z`. Its equality with `s` gives the desired conclusion.
Thus the factors are `1 - C (z i : ℂ) * X`, with multiplicities, without an
inverse or extra shift. All positive ranks and repeated or equal-norm
parameters are retained; no genericity or unitarity hypothesis is imposed
on the spherical class.

Provenance is internal composition of the named Library theorems and the
existing equivalence transport. This module adds a proof of the existing
proposition. It asserts identification of a supplied certificate and does
not assert global existence of pair-polynomial certificates.
