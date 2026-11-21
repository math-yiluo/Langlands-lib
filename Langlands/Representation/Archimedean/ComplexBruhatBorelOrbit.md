# Unipotent and Borel coordinates on the longest complex Bruhat cell

The longest Bruhat cell in complex matrix space of size \(r+1\) is
homeomorphic to the product of the upper unipotent group and the upper
Borel group. The chart sends \((u,b)\) to \(u w_0 b^{-1}\), where \(w_0\)
is the long Weyl permutation matrix. The product group acts by left
unipotent and inverse right Borel multiplication, with the cell as one
orbit.

The chart combines `longestBruhatCellChart` and
`complexTriangularCoordinates`. In the former, a point has the form
\(u w_0 d v^{-1}\) with \(d\) diagonal and \(u,v\) unipotent. The latter
identifies \(d v^{-1}\) with an element of the upper Borel, so its
inverse gives the right Borel coordinate. The multiplication formula
makes the chart equivariant for left multiplication on the parameter
group. If \(p\) moves one point to another, their chart parameters
\(x', y'\) satisfy \(p = y'(x')^{-1}\). For points in specified compact
subsets of the cell the inverse chart therefore bounds all such
parameters in a compact set.

This internal reindexing is used for character-covariant distributions
on the longest cell of the complex principal series.
