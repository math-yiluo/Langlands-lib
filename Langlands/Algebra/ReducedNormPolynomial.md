# The determinant coordinate polynomial

This internal helper defines the actual multivariate polynomial of a finite
family of square matrices. If the family is `M j`, its generic matrix has
entry `sum_j C (M j i k) * X j`, and `detPolynomial M` is the determinant
of this matrix over the polynomial ring. Thus it is a polynomial with
coefficients in the original commutative ring, with no assumption about
infinitude or reducedness of coefficient rings.

`detPolynomial_map` proves that coefficient extension commutes with this
construction. `detPolynomial_eval` proves that evaluation along any ring
homomorphism, at any tuple of values, is the determinant of the resulting
linear combination of matrices. Both proofs use compatibility of the ordinary
determinant with a ring homomorphism, followed by equality of entries.

`detPolynomial_isHomogeneous` states genuine polynomial homogeneity of degree
the matrix size. Each generic matrix entry is a sum of degree-one monomials.
In the Leibniz determinant expansion every product has one entry per matrix
index, and the sign is a constant. Sums preserve that homogeneous degree.
The zero polynomial convention is included in this statement; a later
nonvanishing argument is needed if the exact total degree is required.

For a split algebra chart and a finite family in its source, `chartPolynomial`
is the determinant polynomial of the chart images. Its evaluation equals the
already constructed `splitNorm` on the corresponding tensor linear
combination, over every commutative test algebra. Evaluating the generic tuple
in the polynomial ring itself identifies the polynomial with that split norm.
Chart independence of `splitNorm` therefore proves equality of the actual
polynomials for different charts, including equality of all coefficients.

This is a derived coordinate realization of the determinant convention in
Milne, *Algebraic Groups* (2022 corrected reprint), Remark 24.25, printed
p. 523 / PDF p. 534, registered as `milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The retained author errata snapshot of 2026-11-04 has no correction to that
passage. The polynomial and all-test-algebra statements are internal derived
content, rather than a claim that the remark already proves these statements.
This helper does not yet descend a polynomial from a splitting extension or
construct that extension.
