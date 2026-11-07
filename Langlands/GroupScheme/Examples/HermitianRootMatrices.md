# Matrix realization of diagonal Hermitian root parameters

This internal construction realizes `HermitianRoot.Parameters H` as actual
invertible matrices. It extends the existing three-dimensional coordinate
matrix construction to an arbitrary finite diagonal middle form. Generation
and identification with a group scheme remain separate obligations.

For an involutive commutative ring and fixed diagonal weights `w i`, use the
index type `Unit ⊕ (ι ⊕ Unit)`, in top, middle, bottom order. For a parameter
`(x,z)` with `z + bar(z) = Σ i, w i*x i*bar(x i)`, the matrix is

```text
[ 1   (w i*x i)    z      ]
[ 0       I       bar(x) ]
[ 0       0         1    ].
```

The Gram matrix has top-bottom and bottom-top entries one and middle block
`-diagonal w`; all other entries vanish. `conjugateTranspose` applies the
specified involution and then transposes. `PreservesForm H M` means exactly
`conjugateTranspose M * gram H * M = gram H`.

The matrix map preserves identity and multiplication. The parameter inverse
gives its two-sided matrix inverse and hence the homomorphism `embedding` into
the general linear group. Recovering the vector from the conjugates of the
middle-bottom entries and the scalar from the top-bottom entry proves
injectivity. This does not divide by any diagonal weight.

Nested block-triangular determinant formulas prove determinant one. Expanding
matrix multiplication and the finite sums proves form preservation: every
entry cancels algebraically, with the bottom-bottom entry using precisely the
parameter trace equation. Applying a compatible ring map to all entries proves
coefficient naturality for both the matrices and their general-linear embedding.

These are direct internal algebraic proofs using the already constructed
parameter group, rather than an assertion from the literature. The coefficient
and finite-index universes are independent. The construction uses a decidable
equality on the index type for matrix identity and determinant; it imposes no
field, characteristic, nondegeneracy, anisotropy or nonempty-index condition.
