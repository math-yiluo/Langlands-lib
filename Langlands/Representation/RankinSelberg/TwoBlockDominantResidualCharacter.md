# Residual upper unipotent and its character for the dominant JPSS rectangles

This module constructs the actual residual upper unipotent for the five-block
matrix in Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(2), printed
page 419. The registered original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source supplies the displayed matrix. The residual and its character
calculation are internally derived algebraic data used to formalize its
covariance. Worker 484 supplied the residual design, Worker 1209 supplied the
actual matrix and coordinate helpers, and Worker 1198 implemented these
membership and character proofs.

The scalar field `K : Type uF` has arbitrary universe. With
`a=m 0+1`, `b=m 1+1`, `c=j+k+1`, the hypotheses are
`a+b=t+1` and `r=t+c`; hence the test rank is `r+1=a+c+b`.
Both `j` and `k` are arbitrary natural numbers, including zero. The block order
is `(a,k,1,j,b)`. All rank transport uses the actual ordered equivalence
`coordinates h hr` from the imported matrix module. The subgroup argument
`u` belongs to the actual `lowerBlockUnipotent h K`; its extracted diagonal
blocks `uA,uB` belong to the standard upper unipotent groups.

For `x : Matrix (Fin a) (Fin k) K` and
`y : Matrix (Fin j) (Fin b) K`, write
`LA=w_a*uA*w_a`, `LB=w_b*uB*w_b`,
`Z0=w_b*Z*w_a` and `x'=LA⁻¹*x`. Here the Weyl representatives are the
Library's actual unsigned long permutation matrices. `residualFive` has the
complete five-block formula

```text
[ LA       0           0    0    0  ]
[ 0        I_k         0    0    0  ]
[ 0        0           I_1  0    0  ]
[ y*Z0     -y*Z0*x'    0    I_j  0  ]
[ Z0       -Z0*x'      0    0    LB ].
```

`residualMatrix_five_entry` proves that this is the entry formula of the
actual invertible `residualMatrix`, rather than a matrix supplied by the
caller. It expands the imported three-block residual using the separated
supports of the padded rectangles.

`residualFive_diag` proves that every diagonal entry is one.
`residualFive_above` proves that every entry above the diagonal is zero in
the order given by `position`. Both proofs inspect all five summands. Within
the end blocks, reversing both indices of the extracted upper unipotents
proves the claims. The remaining entries follow from their displayed support
and finite-index bounds. Thus `residualUnipotent h hr u x y` is an actual
element of `upperUnipotent (r+1) K`, with value
`w_(r+1) * residualMatrix h hr u x y * w_(r+1)`.
`residualUnipotent_val` exposes this value. Its membership proof applies the
entry formula for long-Weyl conjugation: reversing finite indices exchanges
upper and lower triangularity and preserves diagonal entries.

For the character calculation, the private middle-subdiagonal lemmas show
that all adjacent lower entries outside the two end blocks vanish. In
particular, the singleton forces each of the four extra rectangle-product
blocks to lie at least two positions below the diagonal. This argument uses
only finite-index inequalities and remains valid when either rectangle has
an empty index set. `residualMatrix_subdiagonal_sum` then splits the sum
into the first `m 0` indices, the `c+1` middle and boundary indices, and the
last `m 1` indices. Only the two end-block subdiagonals remain.

`residualUnipotent_superdiagonal_sum` reverses the complete index set and
then each end block. It identifies the first-superdiagonal sum of the
constructed upper unipotent with the sum of those of `uA` and `uB`.
Consequently, for every topology on `K` and every unitary additive character
`ψ`, `residualUnipotent_character` proves the equality in `ℂˣ`

```text
standardCharacter ψ r (residualUnipotent h hr u x y) =
  standardCharacter ψ (m 0) uA * standardCharacter ψ (m 1) uB.
```

The proof applies the additive character to the proved sum identity and uses
its addition-to-multiplication law. There is no topology hypothesis in the
matrix or sum results; the character result needs only the topology required
by the existing unitary-character type. Matrix covariance and the raw scalar
kernel are supplied by the subsequent modules. No quotient integral,
measure-change law or analytic identity is asserted here.
