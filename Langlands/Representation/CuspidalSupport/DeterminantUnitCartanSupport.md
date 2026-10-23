# Determinant-unit Cartan support bridge

Author: Worker 200. This module supplies the arithmetic step in the forward
Harish-Chandra implication. It imports Worker 237's gap-vanishing helpers.

`finite_zeroSum_boundedGap` proves a finite combinatorial support bound. Subtract
the final coordinate in each block. Antitonicity and the adjacent-gap bound put
every normalized coordinate in a finite integer interval, by the existing
`sub_last_le` lemma. On tuples with zero sum in every block, this normalization
is injective: summing an equality of normalized tuples equates the block size
times their final coordinates. Each block size is positive, so cancellation
equates the final coordinates and then every coordinate. This argument also
handles the empty family of blocks.

`valuation_det_integralRange` proves that the determinant of an integral
invertible matrix has valuation one, using that its determinant is a unit in
the valuation ring. `determinant_torus` computes the determinant of the diagonal
torus element as the uniformizer raised to the sum of its exponents.
`sum_eq_zero_of_cartan` combines these facts with multiplicativity and the
uniformizer's valuation being strictly below one: a Cartan factorization of a
matrix whose determinant has valuation one has exponent sum zero.

`block_sums_eq_zero_of_determinantUnit_cartan` specializes this calculation to
the actual product Levi over a `PadicField` with its compatible topological
data. Membership in `determinantUnitSubgroup` gives normalized absolute value
one for each block determinant. The published normalized-absolute-value and
discrete-valuation equivalence, followed by injectivity of the value-group
isomorphism, gives valuation one and hence zero exponent sum in each block.

These are internal arithmetic and determinant consequences of the bounded-gap
argument used in BZ76 Theorem 3.21. They assume a given Cartan factorization;
they do not prove its existence or the Harish-Chandra equivalence. The
compact-support argument using these finite exponent tuples is implemented
separately.
