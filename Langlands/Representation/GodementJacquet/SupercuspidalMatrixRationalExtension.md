# The rational supercuspidal equation for arbitrary matrix tests

This internal derivation applies the generic Fourier-regular pairing extension
to the actual chosen rational matrix pairings. It uses the established norm-one
covariance of those pairings and the rational equation on Fourier-regular tests.
The all-parameter Fourier-regular operator equation and rational-existence
families remain explicit premises.

`reflectedIotaFourierMatrixCoefficientRationalPairing` postcomposes the actual
Fourier and inverse-transpose rational pairing with the complex algebra
endomorphism given by the normalized spectral reflection `X ↦ q⁻¹/X`. This is a
complex bilinear pairing on full-matrix tests and representation vectors. Its
norm-one right-translation rule is inherited directly from the unreflected
pairing.

For an irreducible supercuspidal representation of rank `n + 1`, where `0 < n`,
and a supercuspidal inverse-transpose pullback, compare this reflected pairing
with the original pairing multiplied by the fixed rational Laurent monomial.
The monomial has unit `shiftedMatrixMonomialUnit F n c k` and exponent `k`;
the scalar correction accounts for the normalized exponent `s + n/2`. Both
pairings have the same determinant-norm-one translation rule. The assumed
global Fourier-regular operator equation makes their restrictions equal,
so the generic extension theorem makes them equal for every full-matrix test.
No convergence-strip exchange is used.

The existing general lemma
`Langlands.GodementJacquet.normalizedFunctionalEquation_of_monomial_rational_identity`
from `MonomialMatrixCoefficientSpan` evaluates a
reflected monomial rational identity wherever the supplied original and dual
reduced denominators do not vanish. Laurent monomials are regular at the
nonzero spectral point. Rational substitution evaluates at `q⁻¹/q⁻ˢ =
q⁻⁽¹⁻ˢ⁾`, giving the normalized functional equation with both denominator
polynomials one and sign exponent zero.

Finally, rational-continuation uniqueness identifies the chosen pairings with
any supplied actual rational values for the test and a pure coefficient
`g ↦ ℓ(ρ(g)v)`. The resulting normalized equation holds for every full-matrix
test with its actual plus Fourier transform. The rational-existence premises
quantify all tests and all vectors for the fixed functional `ℓ`. The unit and
integer in the operator equation are fixed before tests, vectors or functionals.
Extension over the span of smooth matrix coefficients remains a separate step.
