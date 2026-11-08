# Hermitian top-line stabilizer reduction

This internal continuation constructs the last-column root parameter and
reduces the anisotropic top-line stabilizer to an actual Levi matrix.
The coefficient and finite middle-index universes are independent. The
arguments use no characteristic restriction or division by a middle weight.

`lastColumnParameter` assumes full form preservation and a nonzero
bottom-bottom entry `d`. Its vector is `bar(M_middle,bottom/d)` and its scalar
is `M_top,bottom/d`. The bottom-column self-pairing equation proves the root
trace equation after factoring the common denominator out of the finite
sum. The projection lemmas record these coordinates.
`lastColumn_eq_root_column` expresses the last column as `d` times the
recovered upper-root last column. `lastColumn_inverse_root` then uses the
actual root-group inverse multiplication identity to turn it into the
bottom axis with coefficient `d`.

`firstColumn_on_top_of_bottom_eq_zero` uses anisotropy: if the bottom-top
entry vanishes, the first-column self-pairing equation forces its entire
middle part to vanish. The first column therefore lies on the top axis.
`top_entry_ne_zero_of_axis_firstColumn` uses actual invertibility: a zero
top coefficient would make this entire column zero and hence the
determinant zero. `bottom_entry_of_axis_firstColumn` uses the top/last
column pairing equation to prove that the bottom-bottom coefficient is
`1/bar(a)`.

`eq_leviMatrix_of_axis_columns` assumes form preservation, a nonzero top
coefficient, and first and last columns on their respective axes. The
first-column pairing with each middle column makes its bottom entry zero;
the last-column pairing makes its top entry zero. Cancelling the nonzero
hyperbolic coefficients proves both assertions. The complete block matrix
is therefore `leviMatrix a T`, where `T` is its actual middle submatrix.

`exists_root_reduction_to_levi` applies these calculations to an actual
invertible unitary matrix with zero bottom-top entry. It constructs the
last-column root parameter and multiplies its actual upper embedding
inverse on the left. This preserves form preservation and the first axis
column, and removes the last-column cross entries. The two-axis result
identifies the resulting actual matrix with a Levi matrix having nonzero
top coefficient. No generation hypothesis is used.

Combining this factorization with elementary Levi generation, handling
matrices with nonzero bottom-top entry, full-group generation and all
group-scheme and local Kneser–Tits comparisons remain separate obligations.
