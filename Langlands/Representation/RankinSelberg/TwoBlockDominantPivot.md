# The separating singleton in the actual dominant matrix

This is derived internal infrastructure for bounds on the actual matrix in
JPSS (1983), Section 4.10(2), printed page 419, registered source
`jpss-1983-rankin-selberg`. The source's two rectangles avoid its separating
singleton. The lemmas express that feature for the published actual matrix;
they do not assert convergence.

`IsUnitPivot` means that one specified row and one specified column have a
single nonzero entry, equal to one, at their intersection. Such pivots
compose under matrix multiplication. The two source rectangles have this
property at the singleton. The long Weyl and block Weyl permutations move
its row to `b+j` and its column to `t+1+j`. The appended group coordinate
leaves the latter column fixed because it is beyond the group block.
Thus every actual dominant matrix has this isolated unit entry, without
any support, nonvanishing, or integrability assumption, including empty
rectangles.

For any Iwasawa decomposition `M = u diag(a) κ` of any matrix with such an
isolated unit entry, the diagonal entry at the pivot row has normalized
absolute value one. The row of `M κ⁻¹` shows that this diagonal entry is an
entry of the integral matrix `κ⁻¹`. The column of
`κ = diag(a)⁻¹ u⁻¹ M` shows that its inverse is an entry of the integral
matrix `κ`. Both absolute values are at most one, hence each is one.
The proof works for every supplied p-adic topological data and every
integral compact factor; the pivot need not be the last row.
