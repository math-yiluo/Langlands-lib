# Polynomial dependence of the weak constant term pairing

`StandardParabolicFamily.squareIntegrablePairing_polynomial_of_integrable`
proves the polynomial shape of the pairing on the actual standard parabolic
once its integrands are integrable. The inducing form transforms by
\(\delta_P^{1/2}\) on the positive split component. A component with
normalized exponent \(\lambda\) transforms by
\(\delta_P^{1/2}(x)x^\lambda\) times a polynomial in \(H_P(x)\).
The two factors of \(\delta_P^{1/2}\) multiply to the modulus because the
half-modulus is real. Conjugating the second entry contributes the factor
\(\overline{x^\lambda}\).

At each point of the Levi pairing measure the remaining factor is a polynomial
of uniformly bounded degree. Conjugation preserves that degree because the
polynomial space is spanned over \(\mathbb C\) by products of real linear
forms. The theorem `standardPositiveLog` gives finite dimension of the real
character dual and a split-component point for each real character functional.
Dividing the integrand at that point by its nonzero modulus and character gives
an integrable polynomial evaluation. The theorem `exponentPolynomialIntegral`
therefore gives a polynomial of the same degree bound after integration.

`WeakConstantTermComponentPairingIntegrableStatement` states the remaining
analytic assertion for these integrands. Under the log-square-integrable
automorphic hypotheses of `WavePacketWeakConstantTermOrthogonalityStatement`,
it requires integrability for every unitary member of a supplied constant
term decomposition, every square-integrable inducing form, and every
positive split-component point. The integrals use the original maximal
compact and the original norm-one quotient measure.

For provenance, P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, uses the exponent decomposition
in (3.2), p. 10, and the temperedness of each weak constant term in Lemma 3.8
(ii), p. 14. Section 3.4, (3.7) and Remark 3.9, p. 15, give the convergence
and polynomial shape. The registered source `delorme-2023-spectral-theorem-langlands`
contains the published PDF, whose SHA-256 is
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
The absolute convergence there uses the Schwartz estimates for the
square-integrable inducing forms and the tempered estimates for the second
entry. To pass from the total weak term to an individual component, one
can project onto its generalized eigenspace using a polynomial in a
split-component translation. Choose the translation so the finitely many
distinct exponents have distinct character values there. The component is
then a finite linear combination of translates of the weak term. Its
integrability follows from (3.7) at those translated split-component points,
using the inducing form's split-component transformation law.
The source assumes a compact in good position. The stated version
has the compact-subgroup scope of the orthogonality theorem, which calls for
a comparison of the inducing condition and pairing measures.
