# Scalar Tate data and the rank-one JPSS epsilon relation

This internal transport is conditional on actual scalar analytic data,
normalized Laurent generators, and a scalar plus-Fourier functional equation
with a fixed coefficient and exponent. It does not prove the scalar theorem
or the essential/conductor theorem.

`ScalarTateEpsilonData` packages those scalar conclusions at weight one for
a character and its inverse, with one coefficient in `ℂˣ` and one integer
exponent before all tests. Its Fourier witnesses are Schwartz–Bruhat functions
equal to the actual plus Fourier integral, whose integrands are integrable.
The supplied equation holds for every pair of actual rational continuations.
This predicate introduces no assertion that such scalar data exist.

The fixed-functional
transport uses exact scalar/coefficient integral and rational-value comparisons
from `LocalTateModelTransport`. The row/scalar test maps are inverse; scalar
Fourier linearity shows that the Fourier transform of the test absorbing both
coefficient values absorbs the same values on the dual side. The two analytic
packages supply actual rational continuations. The supplied scalar equation
then proves `EqualRankEpsilonEquation` with the same coefficient and exponent.
The second representation is the trivial scalar character, so its
minus-one scalar is one.

For a complex scalar representation, any nonzero equivariant functional is a
nonzero scalar multiple of any other. The coefficient images are therefore
equal by absorbing that scalar into the represented vector. This argument
uses no smoothness premise.

`tateIsEqualRankEpsilonFactor_of_scalar` uses the constructed normalized
rank-one quotient Haar measure and the two identity functionals to supply the
existence clauses of the epsilon relation. Every compatible quotient measure
equals that measure. The coefficient-image equality just proved transfers the
equation to every nonzero functional using
`EqualRankEpsilonEquation.congr_model`.
`tateIsPairEpsilonFactor_of_scalar` then specializes the pair relation to equal
rank one. The resulting factor is exactly `(c, m)`.

The transport is over an arbitrary nonarchimedean local field in an arbitrary
universe, with its Hausdorff and Borel structures on the field, units, general
linear group, unipotent subgroup and quotient as specified in Lean. The
absolute value, natural spectral parameter `q`, character and additive Haar
measure are supplied. Neither characteristic zero nor continuity of the
character is required by this conditional implication.

The provenance is internal: the proof combines the unchanged scalar and JPSS
definitions, the constructed rank-one coordinates and normalized measures,
linear Fourier integration, and the actual coefficient-image transport API.
No source theorem about analytic continuation, generators, epsilon existence,
the conductor exponent or higher-rank essential vectors is proved here.
