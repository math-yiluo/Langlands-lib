# The split Godement integral on the adjacent subgroup

Let \(\Phi\) be a square Schwartz test and \(\phi\) a Schwartz test on the
last column. Write \(n=r+1\) for the smaller rank and \(g\) for an element
of \(\operatorname{GL}_n(\mathbb C)\). `complexAdjacentSplitRestriction`
evaluates the continued Godement integral for the product test at
\(\operatorname{diag}(g,1)\). In the smaller group integral the square
test becomes \(\Phi(hg)\), while the row test is the positive-phase
Fourier integral of \(\phi\) evaluated on the last row of \(h^{-1}\).
The outside factor is \(d((-1)^n)\) times the determinant character
with exponent \(p+n/2\). The determinant weight inside has exponent
\(p+(n-1)/2\).

The proof uses the padded matrix entries to compute the right translate
of a split rectangular matrix. It applies the last-column Fourier
identity and pulls the square test out of the column integral. The
column Jacobian reduces the inner determinant exponent by one, and
padding preserves the determinant in the outside factor. The existing
identity between entrywise and operator-norm Schwartz models preserves
the test values used in these calculations.

This is the split-test specialization of the restriction calculation in
Sections 7.2 and 8.3 of Hervé Jacquet, *Archimedean Rankin–Selberg
Integrals*, 2009, DOI `10.1090/conm/489/09547`.
