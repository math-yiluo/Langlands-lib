# The equal-rank semi-local equation from ordinary tests at complex places

`EqualSemilocalEquationTCFromOrdinaryTestsStatement` derives the totally complex equal-rank
semi-local equation from ordinary Whittaker and Schwartz tests over complex completions
for two actual cuspidal factors of equal rank greater than one. Their ordinary integrals
have nonzero values arbitrarily far to the right.
The tests concern number fields with compact additive adelic quotient and use the prescribed
components of the nontrivial unitary adelic character that is trivial on the number field,
together with the given complex representation parameters.

`infiniteWhittakerSliceModelAt_of_isTotallyComplex` uses the normalized infinite
Whittaker slices for a totally complex field, after viewing the additive character as
a circle-valued character. In rank one the local tests come from Tate theory. In higher
ranks the complex-place functional equation carries nonvanishing of the ordinary
integral to its dual for the same test. There are no real places in these number fields.
The pointwise factorization joins these complex tests with the finite equal-rank JPSS
tests and the factorizable Fourier pair. At each field the proof integrates both pointwise
products with `UnipotentClass.unipotentClassProductStatement`. Both integrals use the same
nonzero measure constant, and the prescribed Schwartz and Fourier product formulas and
nonvanishing assertions carry over. The complex-place equations, the global central sign
and the equal-rank semi-local reduction give the equality with the certified finite gamma
factors.

`equalSemilocalEquationTC_of_ordinaryGeneration` obtains the ordinary tests from
normalized generation and the surjectivity of complex Whittaker restriction. It uses
the equal-rank coverage part of the generation statement.

The factorization argument is the equal-rank case of Cogdell, *Analytic theory of
L-functions for GL(n)* (2004), Theorems 2.2 and 4.1, pp. 211 and 219–220. The complex
functional equation and choice of nonzero tests use Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), Theorems 2.1 and 2.7, pp. 6 and 10.
