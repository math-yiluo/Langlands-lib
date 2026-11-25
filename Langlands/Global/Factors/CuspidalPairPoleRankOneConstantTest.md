# A constant normalized global test for rank-one cuspidal pairs

`RankOneConstantNormalizedTestStatement` gives a single ordinary partial
integral with nonzero constant entire normalization for two actual cuspidal
`GL₁` realizations. Both realizations are trivial on the split centre. The
spectral presentations have irreducible admissible finite components. The test
uses any certified choice of finite L-polynomials and any prescribed real and
complex standard-module parameter families. The finite set contains the two
exceptional sets and supports the finite additive character. Both vectors are
spherical outside it, and the Schwartz function is standard there.

At each retained finite place, `padicRankOneOrdinaryTest` gives an integral
that equals the specified Euler factor throughout a right half-plane. Its
nonzero value on that half-plane makes both chosen Whittaker functionals
nonzero. The finite tensor-factor equivalences then realize those coefficients
with normalized reference vectors. At a real or complex place, the actual
rank-one slice range is the indicated character model. Choose a local vector
with Whittaker value one at the identity and the scalar Gaussian test realizing
the archimedean L-factor. The ordinary normalization at each place is thus one.

The prescribed residual product and pure tensor normalization combine
these local data on the two actual global presentations. The two infinite
products and the comparison of quotient measures give a fixed nonzero scalar.
The formula for the entire normalization of the global test reduces to that
scalar because each local normalized value is one.

This is a derived use of the pure test factorization in Cogdell, *Analytic theory
of L-functions for GL_n* (2004), §4.2, printed pp. 221–222. The rank-one choice
of normalizing tests uses the local scalar results implemented in the Library.
The real and complex Gaussian computations are from Tate (1967), §2.5, printed
pp. 317–319, and the p-adic integer-ring test uses the valuation-shell calculation
on p. 320. The ramified finite test uses the normalized indicator of a compact open
subgroup in the character kernel. The conclusion concerns the ordinary partial
integral for the supplied finite set.
