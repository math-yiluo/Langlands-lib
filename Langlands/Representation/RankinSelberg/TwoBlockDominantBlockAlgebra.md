# Three-block algebra for the dominant rectangular matrix

This module is internal algebra for the actual five-block matrix in JPSS (1983),
Section 4.10(2), printed page 419. The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The residual factor and padding constructions here are derived formalization
infrastructure, not separate displayed claims attributed to the source. The
residual's mathematical design was supplied by Worker 484.

The generic algebra works over every commutative ring `K` in arbitrary universe,
with independently universe-polymorphic finite index types `A,C,B`.
`BlockAlgebra.three` assembles the nine indicated blocks on `A ⊕ (C ⊕ B)`.
`three_one` identifies the diagonal identity, and `three_mul` proves ordinary
three-by-three block multiplication. The proofs split sum-type indices and the
finite sum in a matrix product; they make no assumption that any index type is
nonempty.

For `X : Matrix A C K` and `Y : Matrix C B K` with `X*Y=0`,
`BlockAlgebra.upper X Y hXY` is the actual matrix unit

```text
[ I  X  0 ]
[ 0  I  Y ].
[ 0  0  I ]
```

`upper_val` gives this matrix and `upper_inv_val` gives its inverse with
`X,Y` replaced by `-X,-Y`. Both inverse equations follow from `three_mul`
and the vanishing product.

For actual invertible matrices `LA` on `A`, `LB` on `B`, and an arbitrary
`Z : Matrix B A K`, `BlockAlgebra.lower` is the actual unit
`[LA,0,0; 0,I,0; Z,0,LB]`. Its constructed inverse has diagonal blocks
`LA⁻¹,I,LB⁻¹` and lower-left block `-LB⁻¹*Z*LA⁻¹`. `lower_val` is its
evaluation formula. The two inverse checks use matrix associativity and
cancellation of these units.

Set `X'=LA⁻¹*X` and `Y'=Y*LB`. Their product vanishes by associativity.
`BlockAlgebra.residual` computes the actual unit

```text
upper(X,Y) * lower(LA,LB,Z) * upper(X',Y')⁻¹.
```

Its proved formula `residual_val` is

```text
[ LA     0                  0  ]
[ Y*Z    I-Y*Z*X'           0  ].
[ Z      -Z*X'              LB ]
```

The proof multiplies the displayed blocks, uses `X*Y=0` and inverse
cancellation, and simplifies the resulting entries. `factorization` then
proves the exact identity
`upper(X,Y)*lower(LA,LB,Z) = residual*upper(X',Y')` by group cancellation.
This generic helper asserts no triangular or character property of the
residual; those properties need the specific padded supports and unipotent
diagonal blocks of its later application.

`Middle j k` is `Fin k ⊕ (Fin 1 ⊕ Fin j)`, keeping the separating
singleton explicit. `padX j x` is `x` on the first `k` columns and zero
on the remaining `1+j` columns. `padY k y` is zero on the first `k+1`
rows and is `y` on the last `j` rows. `padX_mul_padY` proves their product
is zero from this disjoint support. `mul_padX` and `padY_mul` prove padding
commutes with multiplication on the external square side. All `j,k : ℕ`
are allowed, including zero. There are no topology, measure, convergence
or analytic hypotheses or conclusions.
