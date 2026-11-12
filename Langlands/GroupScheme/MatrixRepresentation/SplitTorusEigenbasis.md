# A split-torus eigenbasis containing a prescribed eigenvector

This internal derived construction refines the published universal
coefficient-column diagonalization of an actual split-torus representation.

`IsExponentVector I rho m v` states the actual eigenvector equation for the
integer exponent vector m, on every commutative coefficient algebra over the
field and every point of the split torus over that algebra. It permits v=0;
the basis theorems explicitly require the chosen v to be nonzero.

The universal coefficient columns span the representation space and are
universal weight vectors by the published coefficient-column construction.
Adjoin the chosen v to that spanning set. The singleton containing v is
linearly independent. The field-linear basis-extension theorem extends it to
a basis contained in the enlarged spanning set, so every basis vector still
has a universal exponent. Reindexing the basis by the original finite
coordinate type preserves a selected occurrence of v. Its exponent is chosen
to be the original prescribed m.

The matrix whose columns are this basis is invertible. The universal
eigenvector equation in each column gives an intertwining identity with a
diagonal matrix over every coefficient algebra. Conjugating by the same
scalar-extended rational matrix therefore diagonalizes the action everywhere.
Its selected column equals v, and the corresponding exponent is exactly m.
No irreducibility, ambient splitting, or eigenvalue distinctness is required.

This result assumes the chosen universal eigenvector equation. It does not
identify the exponent of a supplied coordinate-line character or assert an
adelic height estimate.
