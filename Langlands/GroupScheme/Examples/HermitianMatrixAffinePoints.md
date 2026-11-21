# Affine coordinates of an actual Hermitian matrix presentation

For a supplied `HermitianMatrix.SchemeModel.Presentation` over a separable quadratic field extension `E/F`, `Presentation.affineMatrixEquiv` identifies points over a commutative `F`-algebra `R` with the determinant-one matrices preserving the Hermitian Gram matrix over `R ⊗[F] E`. The coefficient involution acts as conjugation on `E`, and the Gram entries map through the right tensor inclusion.

The comparison evaluates the global sections of the relative affine test and exchanges the tensor factors. This ring equivalence carries the full Gram equation and determinant condition in both directions. Naturality of relative affine sections and of the original presentation proves compatibility with every algebra map, including those between nonreduced coefficient rings.

This is an internal affine reformulation of the existing all-test presentation. It supplies the matrix coordinates used for the split matrix-algebra case of the special unitary cohomology calculation in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.5.
