# Maximal weighted coefficients of products of linear forms

`Langlands.Analytic.monomialWeight` assigns to an exponent \(d\) the product
\(w^d=\prod_j w_j^{d_j}\). With all \(w_j>0\), the weighted size of a coefficient
\(P_d\) is \(\lVert P_d\rVert w^d\).

`Langlands.Analytic.exists_maximalWeightedCoeff_pos_iff` is a weighted Gauss norm
calculation over an ultrametric normed field. For a product of finitely many
nonzero linear forms indexed by the ordered variables `Fin (n + 1)`, there
exists a maximal weighted coefficient whose exponent of variable \(0\) is
positive if and only if some factor has a maximal weighted coefficient at
variable \(0\).

The proof chooses the least maximizing variable in each factor. Any equally
large product term with the same exponent has the same sum of variable indices.
Each of its indices is at least the chosen one, so equality of their sums
forces all the choices to agree. The ultrametric inequality gives equality
with this unique largest term at the chosen exponent. It also bounds every
coefficient by the size of a term contributing to it, with an empty sum giving
zero. These facts prove the two directions of the criterion, including the
empty product.
