# Smooth completion of complex full-row-rank rectangles

A rectangular complex matrix with one fewer row than columns is completed
by adding a row of conjugated signed maximal minors at the top. The trailing
rows are unchanged. Laplace expansion gives the sum of the squared norms
of the maximal minors as the determinant. Cauchy–Binet, applied to a right
inverse of the rectangle, supplies a nonzero minor on the full-row-rank locus.
The completing matrix is therefore invertible with positive real determinant.
All entries are real-smooth functions of the rectangle, and this also
identifies full row rank with the preimage of the open invertible locus.

The completion gives an explicit chart for the row quotient in Jacquet
(2009), §7.1, proof of Proposition 7.1(v), pp. 45–46. It adapts the
cofactor construction in the Library's real row-completion module.
