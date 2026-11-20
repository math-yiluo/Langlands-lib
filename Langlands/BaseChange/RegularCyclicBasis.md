# Cyclic bases for regular matrices

`cyclicBasisMatrix A v` has columns given by the first `n` powers of the
matrix `A` acting on `v`. This internal construction is used to compare
regular matrices with the same characteristic polynomial.

For a matrix with separable characteristic polynomial, the minimal
polynomial has degree `n`. Over an algebraic closure all characteristic
roots are distinct. Each is an eigenvalue and therefore also a root of
the minimal polynomial, which divides the scalar extension of the
original minimal polynomial. Cayley–Hamilton gives the opposite degree
bound over the original field.

View the vector space as a module over the polynomial ring, with the
indeterminate acting by `A`. Mathlib's theorem for finite modules over
a principal ideal domain supplies a vector whose annihilator equals
the annihilator of the module. Any linear relation on the cyclic
basis columns would give an annihilating polynomial of degree below
`n`. It must vanish, so every coefficient is zero. This proves
`RegularCyclicBasisStatement` by `regularCyclicBasis` for a field of
any characteristic and a matrix of any size.

Over a commutative ring, two matrices commuting with `A` and agreeing
on a cyclic vector agree on each column of the cyclic basis. Inverting
the cyclic basis matrix expresses the image of the vector under a
commuter as a linear combination of those columns. The corresponding
linear combination of powers of `A` is then the original commuter.
All these powers commute with every matrix commuting with `A`.

The cyclic basis matrix maps to the cyclic basis matrix of the extended
matrix and vector under any coefficient homomorphism. Its invertibility
therefore survives scalar extension. This proves
`commute_of_regular_baseChange` for every commutative algebra over the
original field.

For matrices with equal characteristic polynomial, Cayley–Hamilton
gives the same action in both cyclic bases. Column `j` of that action
matrix records the coefficients of `X^(j+1)` reduced modulo the
characteristic polynomial. `cyclicBasis_conjugator` gives the change
of basis as the first cyclic basis matrix times the inverse of the
second. The identity holds over any commutative coefficient ring when
both cyclic bases are invertible.
