# Matrices for a chosen regular-subspace basis

This internal construction exposes the regular representation matrix in any
chosen finite basis of a stable subspace. Its proof is the matrix-coefficient
argument already implemented in `AffineLinearEmbedding.Comodule`, applied to
the given subspace rather than a newly chosen one. Keeping the basis as input
allows a later basis to be adapted to the subgroup ideal.

The file chooses a field-linear retraction onto the subspace and extends its
basis coordinate functionals through that retraction. The coefficient
`M i j` is the left contraction of the comultiplication of the `j`th basis
vector by the `i`th extended coordinate functional.

`comul_basis` proves the actual comultiplication expansion by contraction
with every linear functional. Coassociativity then gives
`Δ(M i j) = ∑ l, M i l ⊗ M l j`, and the counit gives the identity matrix.
`translate_basis` evaluates the comultiplication expansion in any coefficient
module.

`regularRepresentation` then applies the existing coordinate-bialgebra
construction to give an actual `MatrixRepresentation` of the corepresented
group scheme. `regularRepresentation_pointMatrix` proves that its matrix on
every scheme test is evaluation of these coefficients in relative global
sections. No affineness or reducedness condition on the test scheme is used.
