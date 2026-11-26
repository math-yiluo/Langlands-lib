# Spanning the real canonical values by split Godement monomial coefficients

`monomialSplitGenerators D a P Z` is the set of functions in
`realUniformWhittakerModel (r+1) (characterList P Z) (−a)` of the form
`realAdjacentGodementCoefficient D a (realColumnProduct (gaussianPolynomial (monomial d c₀)) φ) U c` with
`U` a value of the smaller canonical Jacquet map `canonicalJacquetMap a (Fin.tail P) (Fin.tail Z)` and
`c = charData (P 0) (Z 0)`.

`canonicalJacquetMap_mem_span_monomialSplitGenerators`: if `Z` lies in the strict spectral chamber and the
leading exponent satisfies the Godement convergence bound `hc`, every value of the larger canonical map
`canonicalJacquetMap a P Z` lies in the span of these generators.

The proof is that of the Library's `RealJacquet.canonicalJacquetMap_mem_span_adjacentSplitGenerators`,
which already uses only monomial generators: `realGodementGaussianSpanning` spans the compact-finite inducing
space by polynomial Gaussian Godement sections, `sectionValue_finset_sum` expands a polynomial into
monomials, `realGodementSchwartzJoint` identifies the canonical value of a section with the Godement
coefficient of its test, and `gaussianMonomial_eq_realColumnProduct` splits a monomial test into a square
monomial and a column monomial. This is the use of Godement sections in Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §10.1, pp. 68–71.
