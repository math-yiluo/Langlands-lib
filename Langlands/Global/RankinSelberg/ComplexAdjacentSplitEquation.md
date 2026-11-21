# The adjacent-rank equation for a continued split Godement value

Fix an adjoining character \(d\), a smaller Whittaker function \(U\)
of character \(\psi_{-a}\), and a split Schwartz test with square
factor \(\Phi\) and column factor \(\phi\). Assume that the left
unitary translates of \(\Phi\) have finite span. The larger function
is the continued Godement value at shift zero for \(d\). The second
Whittaker function is obtained by applying an exact intertwiner to a
compact-finite standard vector.

`complexAdjacentSplitEquation` gives the entire normalized equation
for the resulting adjacent ordinary and dual integrals. It takes as
inputs the smaller equal-rank normalizations and their convergence,
and the compact convolution formula on the second standard vector
and its Whittaker image.

The proof chooses one compact reproducing weight for the ordinary
and dual square tests and applies it under the two unfolded
integrals. Compact convolution then gives a common finite list of
Whittaker vectors and square coefficients. Each summand separates by
Fubini. The square factor uses the positive transform with the
inverse determinant character on the dual side, and the smaller
equal-rank dual test recovers \(\phi\) by row Fourier inversion. The
finite-product normalization multiplies the two factor equations
and gives the smaller central sign to the power \(r+1\).

This is the continued split-test equation in Section 8.3 of Hervé
Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, DOI
`10.1090/conm/489/09547`.

`complexAdjacentSplitDecomposition` gives the finite product formulas on the right half-plane. The square pairs in these formulas have whole-plane normalized continuations with exponential strip growth. `complexAdjacentSplitGrowth` combines them with lower equal-rank pairs having that property. The proof uses the finite product growth theorem and transfers the agreement through both split integral identities, with a common right half-plane for the agreements.
