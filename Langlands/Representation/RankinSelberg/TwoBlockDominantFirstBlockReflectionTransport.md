# Reflected first-block test arguments

Derived infrastructure for the strict-dominant first-block JPSS calculation,
Section 4.9 (printed pages 416–418) and Section 4.10(2) (printed page 419) of
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions* (1983), registered
as `jpss-1983-rankin-selberg`.

`firstBlockReflectedRectangle v z` defines the coordinate substitution
`-w_a v z.transpose` for an invertible `a` by `a` matrix and an arbitrary `q` by
`a` rectangle over any field.

The matrix lemmas combine the previously proved actual inverse-transpose
identity, the commutation of the first-block inclusion with the remaining
columns, and their block-Weyl reversal. The disjoint upper rectangles have zero
cross product, as proved by three-block matrix multiplication.
The unsigned block Weyl is fixed by inverse transpose because it is a
permutation matrix. Hence the translated reflected smaller matrix is exactly the
matrix used in the actual lower kernel, with first rectangle
`-w_a v z.transpose` and remaining rectangle `Y.submatrix Fin.rev Fin.rev`.
This is an algebraic identity for arbitrary complementary row counts, including
zero rows. No convergence or global Laurent identity is asserted here.
