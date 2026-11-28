# Polynomial normalization of the real square zeta integral

`RealSquareZetaPolynomialStatement` applies to a real principal-series
function with specified parity and exponent at every inducing position. The
test is a polynomial in the real matrix entries times the standard square
Gaussian of scale \(\pi\). The square integral uses the supplied real general
linear group Haar measure and the determinant power \(s+r/2\) in rank
\(r+1\). If the raw integrals are absolutely convergent in a right
half-plane, then on a possibly smaller right half-plane they equal a
polynomial in \(s\) times the product of the inducing real Tate factors.

The triangular Haar comparison gives one fixed scalar and a product
integral over the orthogonal group and the multiplicative diagonal. The
spectral determinant power shifts each Tate exponent by \(s\), giving an
additive integral against the product of the one-variable Tate weights. For
each orthogonal element the triangular marginal stays in the
finite-dimensional space of standard diagonal polynomial Gaussians of
bounded degree. Integration against the Tate kernels maps this space
linearly to functions on a common right half-plane. Fubini provides
pointwise integrability in the compact variable, so its integral stays in the
image of this finite-dimensional space. Expanding the diagonal polynomial
into monomials gives a finite linear combination of products of
one-dimensional Tate integrals. This gives the stated factorization, with
the Haar scalar in the polynomial.

The result formalizes the square principal-series calculation used in
[Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7, pp. 30–31 and §8.4, pp. 60–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
