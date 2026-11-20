# Determinants of real matrix conjugation and transpose

`commutatorVectorCLM X` is the linear field `A ↦ X * A - A * X` on the full real matrix space. In the elementary matrix basis the diagonal entry indexed by `(i,j)` is `X i i - X j j`. These entries sum to zero.

Right multiplication is block diagonal in the rows, with one block given by the transpose of the multiplier per row. Its determinant is the matrix determinant raised to the size of the matrix. Transpose identifies left multiplication with the corresponding right multiplication and leaves the matrix determinant unchanged. The two multiplication factors for conjugation by a unit therefore have reciprocal determinants. Transpose itself is an involution, so its determinant has absolute value one.

The identities are auxiliary to the distribution argument in Aizenbud and Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, §7.6.
