# Cuspidal pair L-polynomials and the actual finite integrals

`FinitePairLChoice.IsIntegralPolynomialAt` expresses that the polynomial
specified by the finite choice at a given place is an integral L-polynomial
for the actual embedded local actions. The formulation uses the symmetric
p-adic certificate and the supplied nontrivial character and self-dual
measure, so it applies in both rank orders.

For realizations with unitary central characters, the published finite local
existence theorem gives a class polynomial for that character and measure.
Independence of the normalization data identifies this polynomial with the
one specified in the choice. The class-to-representation comparison gives
the Langlands certificate on the two canonical p-adic realizations. Published
cuspidal local genericity and `IsLanglandsPairLPolynomial.isPadicSymmetricLPolynomial`
then identify it with the integral certificate on those same actions.
Triviality on the split centre supplies the unitary central characters by
`cuspidalSplitCentreUnitaryCentralCharacter`.

This is the comparison used for actual local factors in J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §3.1, Theorem 3.1 (p. 213),
and §4, first two paragraphs of the global setup (p. 218). The registered source
`cogdell-2004-analytic-theory-gln` has these passages on PDF pp. 216 and 221,
with SHA-256 `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The Lean comparison implements the link between the two published certificate
types using their definitions and the generic-case comparison from JPSS (1983),
§9.4, display (4), printed p. 458 (PDF p. 93), formalized by
`genericLanglandsQuotientLFactor`. The registered source `jpss-1983-rankin-selberg`
has SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
