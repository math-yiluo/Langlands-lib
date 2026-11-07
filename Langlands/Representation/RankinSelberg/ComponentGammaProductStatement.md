# Reflected gamma ratio for actual components

`ComponentGammaProductStatement` is an internal assembly statement for two
finite block families in arbitrary positive ranks. The block carriers, the two
component carriers, and the field have independent universe parameters. Each
block and each supplied component is of full Whittaker type for the standard
character. The components are actual irreducible subquotients of the indicated
canonical normalized inductions.

The statement takes certified L-polynomials `P` and `PD` of the component pair
and its actual inverse-transpose pullbacks, and certified polynomials `Q i j`
and `QD i j` of every block pair and its inverse-transpose pullbacks. All dual
certificates use the negated additive character and the same underlying
self-dual Haar measure. It asserts the existence of a nonzero Laurent monomial
`M` such that, with `δ = q⁻¹`,

`(∏ Q i j) / reflectδ(∏ QD i j) = M * P / reflectδ(PD)`.

The precise meaning is `TemperedLFactorGamma.ReflectedRatioData`. The statement
covers both rank orders and does not assert certificate existence, component
genericity, or equality of L-polynomials with the block product.

The provenance is the combination of published gamma multiplicativity for the
two block inductions, `componentFactorComparison` for existing gamma
certificates on actual components of smooth ambient representations, and
`symmetricGammaExpression` for the epsilon-times-L-ratio formula. Full
Whittaker type of the inductions supplies ambient smoothness. Epsilon
coefficients are complex units, so cancelling their products leaves the stated
Laurent monomial. These are the same inputs used for the ambient ratio in
`TemperedLFactorGamma.nonempty_reflectedRatioData`, with gamma comparison
providing the additional passage to the actual components. This is a supporting
interface for the JPSS (8.2) proof, not the component L-factor formula itself.
