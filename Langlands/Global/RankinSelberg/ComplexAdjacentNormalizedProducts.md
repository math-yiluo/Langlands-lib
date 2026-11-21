# Normalizing the adjacent-rank finite product sum

Each summand consists of a smaller equal-rank integral and a square
zeta integral. `complexAdjacentNormalizedProducts` combines entire
normalizations of these factors. The ordinary sum carries the adjoining
sign \(d((-1)^{r+1})\), while the dual sum has unit scalar.

The proof multiplies the entire functions and sums them. The pair
denominator factors by splitting off \(d\) from the larger inducing
list, so the functions agree with the normalized raw sums on a common
right half-plane. For reflection, the equal-rank factor uses parameter
\(-a\) and the square factor uses \(a\). Reversing the square epsilon
parameter contributes \(d((-1)^{r+1})\) and one factor of the smaller
central sign. Together with the equal-rank sign to power \(r\), this
gives the adjacent central sign to power \(r+1\).

This is the factor and sign computation for the finite expansion in
Section 8.3 of Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*,
2009, DOI `10.1090/conm/489/09547`. The hypotheses are the entire
normalizations of the individual factors.

`complexAdjacentNormalizedProductsGrowth` takes lower equal-rank and square normalizations with exponential strip growth and returns that growth for the adjacent pair. It uses the same explicit ordinary and dual finite sums of products as the normalization proof. On each vertical strip the product bounds and the finite-sum bound give the growth of the two functions. The scalar factor on the ordinary function is the same adjoining character value as in the reflection calculation.
