# Gram matrices over a quadratic field

Let `E/F` be a separable quadratic field extension, with conjugation `κ`. The pairing is linear in its first argument and `κ`-semilinear in its second. Its Gram matrix has entry `G(b i, b j)` in row `i` and column `j`. If `P` has the new basis vectors as its columns in the old basis, the Gram matrix changes by `Pᵀ G κ(P)`. Its determinant is multiplied by `det(P) κ(det(P))`. In an orthogonal basis the determinant is the product of the self-values.

Multiplying a Hermitian pairing by a scalar `r` with `κ(r) = -r` makes it antihermitian. With `r ≠ 0`, separation is preserved, so the existing antihermitian orthogonalization gives an orthogonal basis for a finite-dimensional left-separating Hermitian pairing. The diagonal entries in this basis are nonzero. The conversion uses the compatible restriction of scalars from `E` to `F`.

These auxiliary results implement the Gram calculation and diagonalization used in Springer's appendix to Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i), printed pp. 110–111 (PDF pp. 116–117). The norm factor follows by expanding both arguments in the old basis and taking determinants of the matrix product.
