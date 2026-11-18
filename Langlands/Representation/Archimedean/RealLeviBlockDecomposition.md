# Diagonal blocks of real block orthogonal matrices

`diagBlock` extracts each diagonal block. For a matrix with zero off-block entries,
`blockDiagHom_diagBlock` recovers the matrix and `blockDiagHom_injective` recovers
the blocks. If the matrix is orthogonal, each diagonal block is orthogonal.
`orthBlock` records it as an element of the compact orthogonal group, and
`blockDiagGL_orthBlock` reconstructs the original invertible matrix.

`gram_zero_eq` identifies the zeroth Gram determinant with the square of the determinant.
The torus bounds and parabolic integration proofs use these calculations.
