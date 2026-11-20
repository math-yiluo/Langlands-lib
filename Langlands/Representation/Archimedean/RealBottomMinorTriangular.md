# Triangular support of real products of compound matrices

This internal calculation uses the determinant expansion, as in
`JacquetTranslation.minorMat_upper_ne_zero` for complex minors. A nonzero
summand of an upper triangular minor matches each row index to a column index
at least as large. Summing shows that the row index sum is at most the column
index sum. Equality forces the matched sets to agree. The inequalities add
over a family of minors, and their equality conditions hold factor by factor.

For a strictly upper triangular direction, the curve `1 + t X` lies in the
upper unipotent subgroup. Its diagonal minors are constant and its
off-diagonal entries vanish whenever the row sum is at least the column sum.
Differentiation gives the corresponding zero derivative at the identity.
An exponential curve along a diagonal matrix unit gives the column occurrence
count, and the sign reflection gives that count's parity.
