# The reduced norm in matrix Gram coordinates

For a finite-dimensional central division algebra `D` over a field `K`, the matrix
coefficient equivalence identifies `R ⊗[K] M_I(D)` with `M_I(R ⊗[K] D)` for each
commutative `K`-algebra `R` and nonempty finite index type `I`. The homomorphism
`matrixReducedNorm` pulls the actual reduced norm of `M_I(D)` back to these matrix
coordinates. It is natural in `R`.

`matrixReducedNorm_diagonal` computes the norm of a diagonal matrix as the product of
the entry norms. After adjoining an algebraically closed splitting field to the
coefficient algebra, the matrix chart sends the diagonal matrix to a block diagonal
matrix after reindexing. The determinant factors across the blocks. The map from
`R` into the extension is injective, so the determinant identity descends to `R`.

`matrixReducedNorm_adjoint` shows that conjugate transpose preserves the norm for any
first-kind involution on `D`. In the matrix chart the adjoint is transpose followed
by conjugation with a unit. These operations preserve the determinant. Consequently
`matrixReducedNorm_congruence` multiplies the Gram norm by the square of the
change-of-basis norm. These are the diagonal computation and the basis-change
identity behind the skew-hermitian discriminant in Springer's appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §1, printed pp. 105–106
(PDF pp. 111–112).
