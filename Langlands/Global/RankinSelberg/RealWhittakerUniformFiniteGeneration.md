# Uniform growth of real coefficients from finite generation

Let \(d\) be a list of real blocks of total rank \(r+1\). The theorem
`realTiedWhittakerModelUniformity` identifies `realWhittakerModel r d a` with
`realUniformWhittakerModel r d a` for every nonzero additive parameter \(a\)
when all blocks have the same real exponent. This includes purely imaginary
exponents.

Suppose a finite-dimensional subspace of the compact-finite source generates
it under matrix right-derivative words. For any specified coefficient map,
`coefficients_uniformDerivativeGrowth` gives one exponent for every
right-derivative word of each basis vector's coefficient. Take the maximum of
these finitely many exponents. The coefficient map sends a word applied to a
source vector to the same right-derivative word applied to the coefficient.
The estimates for the basis vectors therefore extend by linearity to the
whole source, with a constant that may depend on the source vector. Each
coefficient map in the exact model thus qualifies for the uniform model.

`models_eq_of_irreducible` obtains the generating subspace from the Library's
finite generation over the strictly upper triangular Lie algebra for
irreducible admissible modules. Real standard modules are admissible, and
`realTemperedStandardIrreducible` supplies irreducibility when their real
exponents coincide.

This is an internal consequence of the Library's coefficient estimates and
finite generation theorem. The purely imaginary specialization is the
tempered setting in which Jacquet studies convergence of the local
integrals. [Jacquet, *Archimedean Rankin–Selberg integrals*, Lemmas 5.3 and 5.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
