# Diagonal units of upper triangular invertible matrices

This internal linear algebra helper works over any commutative ring.
The diagonal of a product of upper triangular matrices is the product of
their diagonals. Applying this identity to an invertible triangular matrix
and its triangular inverse proves that every diagonal entry is a unit.
These units define a multiplicative diagonal map.

Removing that diagonal matrix on the right gives an actual upper
unitriangular matrix. Multiplying it back reconstructs the original
triangular matrix. On diagonal matrices the diagonal map recovers the
input tuple.

For a topological ring the diagonal unit map is continuous, since both
its value and its inverse value are continuous matrix entries. Over a
Hausdorff ring the triangular subgroup is closed.
