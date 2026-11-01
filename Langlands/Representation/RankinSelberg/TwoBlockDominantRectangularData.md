# Actual five-block matrices for JPSS Section 4.10

This pair defines the actual matrix in JPSS (1983), Section 4.10(2), and the reversed matrix with right translation in (3), printed page 419. The registered original is `jpss-1983-rankin-selberg`, SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The scan was read directly. The registered index and checked project notes contain no source-specific erratum pointer. The matrix definitions work over any field `K` in any universe; topology is not used here.

For the dependent family `m : Fin 2 → ℕ`, set `a=m 0+1`, `b=m 1+1`, `N=t+1=a+b`, `c=j+k+1`, and `R=r+1=N+c`. The hypotheses are the actual sum equality `h` and `hr : r=t+(j+k+1)`. Both `j` and `k` are arbitrary natural numbers. The source's illustrative choice `k=0` imposes no restriction on these algebraic constructions.

`Coordinates a j k b` is `Fin a ⊕ ((Fin k ⊕ (Fin 1 ⊕ Fin j)) ⊕ Fin b)`. `middleCoordinates` and `orderedCoordinates` collapse these ordered finite sums. The existing `TwoBlockJacquet.blockRanks_add` and `totalRank` prove the rank equalities, and `coordinates h hr` then transports the ordered indices to `Fin R`. Its `coordinates_val` theorem gives the five natural offsets: `0`, `a`, `a+k`, `a+k+1`, and `a+c`. Thus the transports preserve the displayed order, also for empty rectangle dimensions.

For `x : Matrix (Fin a) (Fin k) K` and `y : Matrix (Fin j) (Fin b) K`, `rectangleUnipotent h hr x y` reindexes the actual generic unit with three blocks `(a,c,b)`, using `padX` and `padY` from `TwoBlockDominantBlockAlgebra`. Equivalently, its five identity blocks have sizes `(a,k,1,j,b)`, its `(0,1)` block is `x`, its `(3,4)` block is `y`, and every other off-diagonal block is zero. `rectangleUnipotent_entry` gives the three-block formula; `rectangleEntries` and `rectangleUnipotent_five_entry` give all twenty-five blocks explicitly. The padding supports are disjoint, so their product vanishes. The generic inverse formula, together with the fact that padding commutes with negation, proves `rectangleUnipotent_inv`: the inverse replaces both rectangles by their negatives.

`blockWeyl h hr` is the actual block sum `diag(w_a,w_(c+b))`, transported only along the proved rank equality. All Weyl matrices are the Library's unsigned anti-diagonal permutation matrices. `blockWeyl_mul_self` follows from their involution and the block-sum homomorphism. `append hr` transports the existing `appendIdentity t c` into the actual target rank; `append_entry` proves that it is exactly `diag(g,I_c)`.

The requested declaration `Langlands.RankinSelberg.TwoBlockDominantRectangular.matrix` is

```text
matrix(h,hr,g,x,y) = w_R * rectangleUnipotent(h,hr,x,y)
                       * diag(w_a,w_(c+b)) * diag(g,I_c).
```

`matrix_eq` proves this evaluation law in the actual general linear group, exposing the rank transport on the block-Weyl factor. Its entries and all factors are actual matrix units, rather than caller-supplied abstract operators.

`rightWeyl hr` is the actual block sum `diag(I_N,w_c)`, transported along `N+c=R`. `reversedMatrix` uses the complete reversed family `i ↦ m i.rev`, its proved sum equality, and exchanges `j,k`. Its rectangles therefore have sizes `b×j` and `k×a`, and its five blocks are `(b,j,1,k,a)`. `reversedMatrix_eq` identifies it with precisely that construction followed by `rightWeyl hr`. These are the matrix factors displayed in 4.10(3); no dual section or analytic functional equation is asserted.

This pair also constructs the raw residual unit needed by the descent proof. For the actual lower-group element `u`, `crossMultiplier h u` reads the actual `(1,0)` block `Z` at reversed indices. `crossMultiplier_eq` proves that this is `Z0=w_b Z w_a`, using actual rectangular multiplication by the unsigned Weyl matrices. `residualMatrix h hr u x y` reindexes the generic `BlockAlgebra.residual` with `LA=leftMultiplier h u`, `LB=rightMultiplier h u`, `X=padX j x`, and `Y=padY k y`. Its `residualMatrix_entry` law is exactly

```text
[ LA       0                    0 ]
[ Y*Z0     I-Y*Z0*(LA^-1*X)      0 ]
[ Z0       -Z0*(LA^-1*X)         LB].
```

The generic residual is a product of actual invertible matrices, so this definition requires no covariance premise. Upper-unipotent membership after long-Weyl conjugation, the character identity, and matrix and raw-kernel covariance are separate helper units of the task.

The source supplies the five-block matrices. The coordinate equivalence, residual formula and descent design are internally derived mathematical support supplied by Worker 484, credited as a coauthor. The ordered rank transports and compatibility proofs are internal formalization details. This pair asserts no Haar preservation, quotient integral, integrability or analytic identity.
