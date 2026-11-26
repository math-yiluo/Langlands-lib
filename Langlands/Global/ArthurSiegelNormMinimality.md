# Norm minimality on Arthur's Siegel sets

`ArthurSiegelNormMinimalityStatement` compares the full adelic height of a point
in an Arthur Siegel set with the height of any rational left translate of that
point. The comparison constant is uniform over both points and translates. The
statement uses the full maximal split torus, including the central directions.
It uses any compact Iwasawa subgroup and any compact factor data defining the
Siegel set. The normalized matrix height must have positive matrix size.

The proof identifies the Iwasawa height evaluated on a character of the maximal
split torus with the logarithm of the character's normalized idelic norm. A
lower bound for the values of the finitely many simple roots at the chamber
parameter gives one positive lower bound for all simple-root norms on the
chamber. This includes the empty simple-root set.

`exists_adelicHeight_map_le_rational_mul` bounds the height of the torus point
by the height of each of its rational translates. The compact unipotent
conjugation estimate and commutation of the minimal Levi with the torus then
give the comparison for the product with the compact factors, by
`exists_adelicHeight_le_mul_rational_of_maximalSplit`. These estimates yield
`arthurSiegelNormMinimality`.

The bound is the height comparison used in Arthur 1980, Lemma 1.4, printed
p. 96 (PDF p. 11), and Arthur 2005, Proposition 13.2, printed p. 72 (PDF
p. 84). The proof derives the comparison for the normalized adelic matrix
height and the full-torus Siegel sets from the Library's diagonal bound and
standard-root estimates.
