# Matched real triangular expansions

`Langlands.GodementJacquet.RealTriangularMatchedStatement` and
`realTriangularMatched` give two integral expansions with the **same**
positive Haar constant. This is an internal step toward Jacquet (2009), §4.7,
pp. 30–31, especially the weighted matrix integrals in (4.4). It is not the
coefficient functional equation.

Put \(n=r+1\), \(G=\mathrm{GL}_n(\mathbb R)\), and \(K=\mathrm O(n)\). Fix a
left Haar measure \(\mu\) on \(G\), an s-finite Haar measure \(\kappa\) on
\(K\), and \(b\in\mathbb R^\times\). All additive entry measures used below
are self-dual for \(\psi_b(x)=e^{2\pi i b x}\); for Jacquet's transform with
\(\psi=\psi_a\), use \(b=-a\). Let \(d^\times d\) be the product of
\(dx/|x|\) on the full diagonal units. The constant \(c>0\) depends only on
these measures, not on the test or inducing data.

Let \(f\) be a smooth normalized principal-series section for the inducing
functions \(\chi_i\), \(\Phi\) a square matrix Schwartz function, and \(h\)
a measurable complex function on the real line. Write \(\iota(g)=g^{-T}\).
For \(k\in K\) define the Schwartz test \(F_k(d)\) on real diagonal entries
by integrating \(\Phi(T(d,x)k)\) in the strict upper entries \(x\) of
\(T(d,x)\), where \(T(d,x)\) is upper triangular with diagonal \(d\).

* If \(\Phi(g)f(g)|\det g|^{r/2}h(|\det g|)\) is integrable against \(\mu\),
  its integral equals \(c\) times the integral on \(\kappa\times d^\times d\)
  of \(\prod_i\chi_i(d_i) f(k) F_k(d) h(\prod_i |d_i|)\). This last
  integrand is integrable on that product.
* If \(\widehat\Phi_b(g) f(\iota(g))|\det g|^{r/2}h(|\det g|)\) is integrable
  against \(\mu\), its integral equals \(c\) times the integral on the same
  product of \(\prod_i\chi_i(d_i^{-1}) f(k)\widehat F_{k,b}(d)
  h(\prod_i |d_i|)\). This last integrand is integrable on that product.

The proof unfolds the full triangular Haar pushforward and permutes the
factors to apply Fubini to the strict upper-entry variable first. In the
primal integral, row scaling takes the strict entries of the unipotent
factor to those of the upper triangular matrix; its Jacobian, the
principal-series half modulus and the rank shift combine to the diagonal
weight above. In the dual integral change \(g\) by \(\iota\), invert the
full diagonal and invert the unipotent factor. The changes preserve the
respective measures; see `RealTriangularInversion`. The resulting matrix
argument of \(\widehat\Phi_b\) is the transpose of the column-scaled
upper triangular matrix, multiplied on the right by \(k\). The column
Jacobian gives the inverse-character weight. Right translation by \(k\)
commutes with this Fourier transform because its determinant has absolute
value one and \(\iota(k)=k\). The complementary triangular Fourier
marginal then gives exactly the diagonal transform of \(F_k\).

The module also identifies `matrixTransform` pointwise with the Library's
`realRectangularSchwartzFourier` at square sizes by expanding
\(\operatorname{Tr}(X^T Y)\) as the entry pairing. It uses that
identification for left–right Fourier covariance. The integrability
premises are per side; this module does not establish absolute convergence
of the group integrals or compare the two diagonal integrals by Tate theory.
