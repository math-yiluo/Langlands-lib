# Determinant density for complex general linear Haar measure

`complexGeneralLinearHaar` takes the product Lebesgue measure on the square
complex matrix space, restricts it to the invertible locus and uses the
density \(|\det g|_{\mathbb C}^{-n}\), with \(|z|_{\mathbb C}=\|z\|^2\).
It is left and right Haar measure on the actual group of matrix units.

The proof of the scaling law uses the published change of variables on a
single complex row. Right matrix multiplication acts separately on all
rows, so the product measure picks up the product of their determinants.
Transpose preserves the entrywise measure and carries right multiplication
to left multiplication. The published determinant-density theorem therefore
gives left Haar measure. The modular character is trivial on scalar matrices
by centrality and hence trivial on the whole group by the published general
linear group argument. This gives right invariance.

`integrable_complexGeneralLinearHaar_iff` applies the density formula to
absolute integrability on the invertible matrix locus.

This is a derived measure construction for the matrix integration in
Jacquet's Lemma 3.3 and the Godement integral (7.1). [Jacquet, *Archimedean Rankin–Selberg integrals*, pp. 13 and 43](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
