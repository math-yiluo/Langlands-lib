# Actual lower-group covariance of the dominant JPSS matrix

This module proves the actual matrix factorization underlying descent of the
five-block matrix in Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(2),
printed page 419. The registered original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source supplies the displayed matrix. The coordinate reflection,
rectangle change, residual and covariance proof are internally derived
algebraic support. Worker 484 supplied the residual and rectangle-change
design; Worker 1209 implemented the actual matrices and factorization;
Worker 1198 supplied the imported residual membership and character proofs.

The field `K : Type uF` has arbitrary universe. Retain the dependent family
`m : Fin 2 → ℕ`, its sum equality `h`, and `hr : r=t+(j+k+1)`.
Write `a=m 0+1`, `b=m 1+1`, `N=t+1=a+b`, `c=j+k+1`, and
`R=r+1=N+c`. The ordered five blocks have sizes `(a,k,1,j,b)`.
Both `j` and `k` are arbitrary naturals, including zero. No topology is
needed for this module. All matrices are actual general-linear group elements.

`splitCoordinates a d n H` identifies two consecutive finite blocks with
`Fin n` using their sum equality. `splitReflection` reverses each block
without interchanging the blocks; its inverse is itself. `blockWeyl_permutation`
identifies the actual unsigned block-Weyl matrix
`D=diag(w_a,w_(c+b))` with this permutation. The entry proof checks both
diagonal blocks and the vanishing off-diagonal blocks.

`reflectedIndex` gives the action of this permutation on the already ordered
`coordinates h hr`. For a first-block index `i`, its value is `i.rev.val`;
for a middle index `z`, it is `N+(middleCoordinates j k z).rev.val`;
and for a final-block index `i`, it is `a+i.rev.val`.
`splitReflection_coordinates` proves these formulas by finite-index
arithmetic. Thus the reflected order is the source inclusion order `(a,b,c)`,
with internal reversals, rather than a rank identification that silently
permutes blocks. `blockWeyl_conjugate_entry` proves that conjugating any
actual matrix by `D` evaluates both indices at `reflectedIndex`.

The first and final reflected blocks lie in the first `N` coordinates and
agree with the existing two-block indices, with reversed internal indices.
The reflected middle block lies outside those coordinates.
`reflectedIndex_injective` records injectivity of the complete reflection.
Using these facts, `blockWeyl_append_lower` proves

```text
D * diag(u,I_c) * D = [ LA  0  0  ]
                      [  0  I  0  ]
                      [ Z0  0  LB ],
```

in the target coordinates `(a,c,b)`. Here `u` belongs to the actual
`lowerBlockUnipotent h K`, its extracted blocks are `uA,uB,Z`, and
`LA=w_a*uA*w_a`, `LB=w_b*uB*w_b`, `Z0=w_b*Z*w_a`.
The proof evaluates all nine blocks. It uses the actual upper-right-block
vanishing of `u`, the entry laws for the extracted diagonal blocks and
`crossMultiplier`, and the identity entries in the appended complement.

Let `U=rectangleUnipotent h hr x y`, `x'=LA⁻¹*x`, `y'=y*LB`, and let
`L=residualMatrix h hr u x y`. The imported block algebra computes

```text
L = [ LA       0                    0  ]
    [ Yhat*Z0  I-Yhat*Z0*(LA⁻¹*Xhat) 0  ]
    [ Z0       -Z0*(LA⁻¹*Xhat)       LB ],
```

where `Xhat` and `Yhat` are the singleton-separated padded rectangles.
`rectangle_lower_factorization` transports the proved generic block
factorization to the actual rank and proves

```text
U(x,y) * D * diag(u,I_c) * D = L * U(x',y').
```

The padding multiplication laws identify the transformed padded rectangles
with the paddings of the actual `x',y'`; there is no caller-supplied
factorization premise. This argument also applies when either rectangle
has an empty index set.

`matrix_covariance_raw` uses this factorization, the actual inclusion
homomorphism, and the involutions `D²=1` and `w_R²=1` to prove

```text
matrix(h,hr,u*g,x,y) = (w_R * L * w_R) * matrix(h,hr,g,x',y').
```

`matrix_covariance` gives the same equality with the computed standard
upper-unipotent element `residualUnipotent h hr u x y` and the two projections
of `rectangleChange h j k u (x,y)`. Its membership and exact positive
product character law are proved in the imported residual-character module.
The actual matrix, the residual and the simultaneous rectangle change are
all fixed constructions; none is an additional covariance hypothesis.
This unit supplies matrix covariance for the raw-kernel consumer. It makes
no assertion about fixed-rectangle quotient invariance, Haar measure,
integration, convergence, dual sections or an analytic identity.
