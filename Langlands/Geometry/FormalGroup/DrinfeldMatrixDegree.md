# The degree of the actual matrix action on a formal frame

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2 A,
printed p. 109 (PDF p. 3), chooses matrix coordinates on the rational
endomorphisms of the special frame. His action formula uses the
normalized determinant order for the matrix component. Harris,
*Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces* (1997), Appendix, printed p. 112 (PDF p. 38), defines
quasi-isogeny height by a logarithmic difference of actual kernel
ranks after clearing a denominator. The formal module here uses
powers of the uniformizer and the residue cardinality \(q\).

`MatrixCoordinates.degree` first applies the chosen coordinates to the
invertible matrix and forgets the order equivariance. It then uses the
positive rational degree of the actual quasi-isogeny, computed as the
ratio of the integral numerator rank and the scalar denominator rank.
The degree is multiplicative and agrees with the rational division
action on central scalars, since both actions extend the original
scalar action.

For a character \(\chi\) with positive rational values and matrices of
size \(d\), the character \(\chi(g)^d/\chi(\operatorname{scalar}(\det g))\)
is one on central scalars by the determinant of a scalar matrix.
Take its real absolute value and apply the general linear character
lemma from `GeneralLinearUnimodularity`. That lemma uses transvections,
diagonal matrices and permutation symmetry. Positivity gives the
equality of the rational \(d\)-th powers before taking absolute values.
The division-action formula gives the scalar degree, with reduced-norm
order \(d\) times the scalar order. Injectivity of the \(d\)-th power
on positive rationals then gives \(q^{H\,\operatorname{ord}_K(\det g)}\)
when the formal module has scalar height \(Hd\). The frame of scalar
height \(d^2\) takes \(H=d\).
