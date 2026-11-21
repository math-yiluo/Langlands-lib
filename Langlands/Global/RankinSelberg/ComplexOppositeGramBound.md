# Tail Gram determinants control complex opposite-cell coordinates

Let u be an upper-unitriangular complex matrix and let R be the product of
the Gram determinants of the tail rows of its transpose. Then R is at least
`1 + ‖u − 1‖²` for the entrywise supremum norm.

Cauchy–Binet expresses each Gram determinant as a sum of squared absolute
values of minors. The principal minor contributes one. For a strict upper
entry u(j,i), with j < i, use the tail rows beginning at i and replace the
first tail column i by column j. The resulting square submatrix of the
transpose is lower triangular. Its first diagonal entry is u(j,i), and the
others are one. These two distinct column sets contribute at least
`1 + |u(j,i)|²` to the Gram determinant. Each other tail determinant is at
least one. The entrywise bound follows since the diagonal and strict lower
entries of u − 1 vanish. The product is one in rank zero.

This is an internal estimate for polynomial moments on the opposite cell. It
uses the bottom-right minor and Gram definitions in
`ComplexStandardNontrivialProof` and the finite Cauchy–Binet identity.
