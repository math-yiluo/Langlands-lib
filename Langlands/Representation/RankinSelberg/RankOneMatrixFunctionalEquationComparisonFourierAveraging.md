# Fourier-compatible averaging of actual model functions

This internal derived module chooses a compact open subgroup from an original
full-matrix Schwartz test alone. It constructs an actual normalized bi-smooth
coefficient on the specified coefficient model and preserves the original and
inverse-transpose integrals against every supplied Fourier partner, assuming
convergence of both original integrands.

The construction composes Worker 396's paired compact average with Worker 623's
actual Fourier covariance and compact determinant-norm identities. Its
provenance is this composition of proved identities, rather than an additional
analytic existence assertion. The field and original representation-carrier
universes remain independent. All Fourier expressions use the supplied
character and scalar Haar measure.

`matrixTestAveragingSubgroup` chooses a subgroup from
`exists_compactOpen_matrixTest_invariant`. Its specification gives compactness,
left invariance of the original test, and determinant norm one.
`inverseTransposeOpenSubgroup_toSubgroup` identifies the preimage used in
averaging with the image used in Fourier covariance: inverse transpose is
involutive. `matrixTestAveragingSubgroup_fourier_spec` applies the actual
Fourier-pair invariance theorem to this subgroup, and compactness of its
inverse-transpose transport proves determinant norm one there.

`fourierAveragedModelCoefficient` is the normalized actual model coefficient
using that chosen subgroup. It depends on the original test and model vector,
but not on the Fourier partner. Its paired integral theorem specializes the
previous paired averaging theorem, at arbitrary respective parameters, to any
actual Fourier pair. Both original convergence assumptions are retained;
convergence cannot be recovered by reversing compact averaging.

`fourierAveragedModelCoefficient_rationalValues_iff` assumes shifted
convergence of the original function against the original test and of its
inverse transpose against the Fourier test. It intersects the two convergence
half-planes and applies paired preservation at `s + jpssShift n`. Thus both
averaged functions converge there, and their shifted integrals agree with the
original ones. `RationalContinuationLinear.continuation_of_eq_on_right`
transfers any specified rational continuation in both directions. The
residue parameter in this equivalence is an arbitrary natural number; the
two rational expressions are preserved exactly.

`normalizedMatrixFunctionalEquationData_model_values` applies actual normalized
matrix data on the supplied coefficient model to the single averaged
coefficient. The original rational-value hypotheses contain both original
convergence witnesses, so the equivalences transfer them to that coefficient.
The result gives the normalized equation for every original model vector and
every pair of its original and inverse-transpose rational values. Its Fourier
witness depends only on the original test, as in the matrix-data premise. It
retains the canonical residue cardinality, the proposed polynomials, unit and
integer, the central scalar `1`, and sign exponent `0`.

`normalizedMatrixFunctionalEquationData_model_exists` uses both analytic
assertions in the same matrix-data premise to obtain rational values for
the averaged coefficient and its inverse transpose. Assuming both original
shifted convergence assertions, the equivalences transfer those values back
to the original model functions. Applying the supplied equation to the same
averaged coefficient proves the normalized equation for these values.

These are conditional analytic transfers: unconditional convergence of the
original model functions, nonvanishing for their value family, the Weyl
substitution, and the positive-rank block comparison remain separate
obligations for the final all-rank gamma comparison. Self-duality of the
scalar measure is unnecessary for these conditional assertions, since the
Fourier pair is supplied in each use.
