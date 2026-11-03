# Tensor subspaces in adapted coordinates

This internal bridge expresses the previously constructed tensor-image
stabilizer criterion in the matrix coordinates of a chosen finite basis.
`basisTensorVector` is the actual sum of basis vectors tensored with their
coefficients. Contraction by the extended basis coordinates recovers each
coefficient.

If a subspace is spanned by a selected subfamily of that basis, such a tensor
belongs to its scalar extension exactly when every outside coefficient
vanishes. The forward proof contracts a tensor-image witness by a coordinate
which vanishes on the subspace. The reverse proof supplies an explicit
tensor-image witness for each remaining summand.

For a stable coalgebra subspace, `stabilizes_iff_matrix_columns` applies the
proved translation formula to identify preservation with vanishing of the
outside entries of the selected matrix columns. It tests the chosen
generators and extends to the entire subspace by linearity. These statements
work for arbitrary coefficient modules and thus apply to all coefficient
algebras, including nonreduced ones.

The final `stabilizes_iff_matrix_preserves` identifies this tensor-image
condition with actual preservation of the corresponding coordinate span by
the evaluated matrix. Matrix linearity extends the selected-column
condition to the full submodule over the coefficient ring.
