# Finite products in the unfolded complex adjacent-rank integral

Suppose the averaged smaller Whittaker factor has a finite expansion
\(V(g,z)=\sum_j W_j(g)C_j(z)\). If each square factor and each smaller
equal-rank factor is absolutely integrable, `complexAdjacentProductExpansion`
evaluates the joint integral as the sum of products of their integrals.
The proof distributes the finite expansion in the integrand, uses
absolute integrability of each product to exchange the finite sum
and the integral, and integrates each product on the product measure.

The module also relates the split Fourier tests to the functional
equations used on the factors. The positive square transform is the
Library's square transform at parameter \(-a\). The row transform of
the ordinary split test at parameter \(-a\) recovers the original
last-column test. These equalities follow from sign reversal in the
trace character and row Fourier inversion.

This packages the finite product step in Section 8.3 of Hervé Jacquet,
*Archimedean Rankin–Selberg Integrals*, 2009, DOI `10.1090/conm/489/09547`.
