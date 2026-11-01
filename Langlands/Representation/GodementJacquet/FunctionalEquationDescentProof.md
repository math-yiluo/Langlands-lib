# Descent of normalized matrix functional-equation data

`normalizedMatrixFunctionalEquationDescent` proves the closed internal
`NormalizedMatrixFunctionalEquationDescentStatement`. The two representation
carriers and the field have independent universes, and the rank includes `n = 0`.
All topological hypotheses, the self-duality of the supplied scalar Fourier
measure, the coefficient inclusion, both memberships of one, and the full ambient
data remain explicit premises.

The proof includes each target rational-value family into its ambient counterpart
by retaining the same test function, coefficient function and continuation. It
restricts the ambient common convergence bounds and continuation assertions in
the same way. Each ambient normalized generator supplies a common denominator;
restriction preserves that denominator. The published
`normalizedGeneratorExistence` then uses the corresponding target membership of
one to construct new normalized polynomials `Q` and `QDual`. The proof does not
assert that the ambient generators still generate the target modules.

The supplied self-dual scalar measure gives the full rectangular Schwartz Fourier
equivalence `T`. Its forward evaluation identifies the ambient Fourier witness
with `T Φ`. For every target coefficient and every actual continuation pair, the
ambient normalized equation implies a rational gamma identity through
`NormalizedFunctionalEquation.rational_gamma_identity`. The published
`gammaFunctionalEquation_of_rational_identity` expresses that identity on the full
reduced-denominator domain.

For each ordinary target value, rationality at `T Φ` supplies a related transformed
value. Conversely, for every transformed value at `Ψ`, rationality at `T.symm Ψ`
supplies an ordinary value; Fourier surjectivity identifies its transform with
`Ψ`. The resulting two incidences, together with the new normalized generators,
are precisely the hypotheses of `gammaNormalization_of_incidence`. That existing
theorem constructs a new complex unit and integer exponent and converts every
related gamma equation into the required normalized equation.

The final package retains both analytic assertions and chooses `T Φ` before
quantifying over target coefficients and their continuation pairs. The Fourier
pair still uses the supplied scalar measure and its square product, the plus
transpose convention, and pointwise integrability. The equation retains central
scalar `1`, sign exponent `0`, the inverse-transpose coefficient, the original
shift and spectral parameter, and both continuation denominator guards.

This is an internal derivation from the cited Library declarations, with no new
literature theorem asserted. It proves a conditional descent implication, not
unconditional analytic existence or the host
`GenericMatrixFunctionalEquationStatement`. Worker 364 implemented the proof;
Worker 704 supplied the descent route and identified the existing normalization
and Fourier APIs.
