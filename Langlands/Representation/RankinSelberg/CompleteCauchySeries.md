# Two-alphabet complete symmetric Cauchy series

Author: Worker 1767.

This internal algebraic development constructs the product, over a second
finite alphabet of positive size, of the complete symmetric generating series
in a first finite alphabet rescaled at each second variable. The alphabet
sizes are independent. Jacobi–Trudi in the first alphabet is defined at the
matrix rank of the second alphabet.

The formal Schur coefficient theorem, together with coefficient-ring transport,
identifies its degree `d` coefficient with the sum over degree `d` partitions
of the first-alphabet Jacobi–Trudi polynomial times the second-alphabet
Jacobi–Trudi polynomial. This coefficient expansion is proved over coefficient
domains and takes place in a nested multivariate polynomial ring.

For every commutative coefficient ring the constructed series times the product
of all linear pair factors `1 - x_i y_j t` is one. This follows by transporting
the complete symmetric inverse elementary-product identity into the nested
ring, rescaling at each second variable, and multiplying over that alphabet.
The identities are formal; specialization and analytic convergence remain
separate obligations.
