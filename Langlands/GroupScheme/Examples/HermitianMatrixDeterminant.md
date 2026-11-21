# Determinants of Hermitian isometries

`UnitaryDeterminantSurjectivityStatement` asserts that every unit of conjugate norm one in a separable quadratic field extension is the determinant of an isometry of any nonsingular Hermitian form of positive dimension. `exists_unitary_det_eq` proves it by choosing an orthogonal basis and scaling one line by the specified unit. The diagonal isometry has the specified determinant, which is invariant under the change of basis. `bar_det_mul_det_eq_one` shows that every isometry determinant has conjugate norm one by taking determinants in the preservation equation. That implication holds over any commutative coefficient ring with involution.

`adjointUnit` equips the adjoint of an invertible matrix with its inverse. `Form.inverse` is the Hermitian form with inverse Gram matrix. The column isometry equation for a Gram matrix is equivalent to the row isometry equation for its inverse. These identities hold over the full coefficient ring.

The determinant calculation gives the matrix-algebra case of the norm adjustment used in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.5.
