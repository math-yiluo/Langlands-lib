# Signed kernel-rank height of the matrix action on the source cover

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2 A,
printed p. 109 (PDF p. 3), precomposes the framing by the inverse
matrix in the chosen coordinates on the rational endomorphisms.
Harris, *Supercuspidal representations in the cohomology of
Drinfel'd upper half spaces* (1997), Appendix, printed p. 112
(PDF p. 38), defines the height as the logarithmic difference
between the kernel ranks of an integral numerator and the scalar
denominator. Here the denominator is a power of the uniformizer
and the logarithm has base the residue cardinality \(q\).

`MatrixCoordinates.heightPresentation` uses the positive rational
degree of the matrix quasi-isogeny to choose a ranked integral
numerator. For scalar height \(Hd\), where \(d\) is the reduced
degree, the numerator and scalar denominator give the signed
index \(H\,\operatorname{ord}_K(\det g)\).

On a height-\(d^2\) frame the comparison takes \(H=d\). Coefficient
extension along the residue map preserves the ranks in the
presentation. Restriction to the original reduced source cover
gives the same index on every chart test. For the inverse matrix
used in the framing formula this is
\(-d\,\operatorname{ord}_K(\det g)\), since the normalized order
of the determinant changes sign under inversion.
