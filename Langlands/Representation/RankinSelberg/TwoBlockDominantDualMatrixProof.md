# Proof of the actual reversed-dual dominant matrices

`Langlands.RankinSelberg.twoBlockDominantDualMatrix.{uF}` proves exactly
the existing closed proposition
`Langlands.RankinSelberg.TwoBlockDominantDualMatrixStatement.{uF}`.
Its theorem type has no additional comparison premises. The module imports
the unchanged statement and the published
`TwoBlockDominantCovarianceData`, whose block-reflection permutation
description is reused in the proof.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), Section 4.10, printed pp.418–420: the two five-block
matrices are in formulas (2) and (3) on p.419, and the three-Weyl identity
is displayed on p.420. The registered source is
`jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These are one-based PDF pages 53–55, or zero-based indices 52–54.
The original page images were read, and the registered index and checked
project errata locations provide no source-specific correction.

Write `a=m 0+1`, `b=m 1+1`, `N=t+1`, `c=j+k+1`, and `R=r+1`.
The supplied rank equalities imply `N=a+b` and `R=N+c`.
The source's ranks `t,r,t₁,t₂` correspond respectively to `N,R,a,b`.
The original five-block order is `(a,k,1,j,b)`; its reversal is
`(b,j,1,k,a)`. The proof retains the entire reversed family
`mD i=m i.rev`, the existing proof `reverse_sum h` of its rank equality,
and the complementary-size equality derived from `hr` by arithmetic.

The source motivates the matrix comparison. The explicit signed
coordinates, its packaging as the closed proposition, and the extension
to arbitrary fields and arbitrary complementary `j,k` are derived algebraic
support. The implemented proof is a finite permutation and matrix
calculation; it does not invoke the paper's functional equations or any
gamma/L-factor theorem.

All supporting declarations are private to the namespace
`DominantDualMatrixProof`. The proof has three parts.

First, `splitReflection_val` computes the natural value of reflection
inside two successive blocks of sizes `a,d`, with `a+d=n`:
it is `a-1-i.val` in the first block and `n+a-1-i.val` in the second.
The proof transports an arbitrary index through the published
`splitCoordinates` equivalence and handles its two summands. The helpers
`reindex_permutation` and `blockSum_permutation` identify reindexed
permutation matrices and block sums of permutation matrices by their
entries. They yield `splitWeyl_permutation`.

The helper `append_blockSum` identifies the actual `append hr g`
with the reindexed block sum `diag(g,I_c)`, using the published
`append_entry` and all four pairs of block summands. Consequently
`append_weyl_right` identifies
`append hr w_N * rightWeyl hr` with the permutation reflecting the
two blocks of sizes `N,c`. The published `blockWeyl_permutation`
identifies the two other block-Weyl matrices. In `threeWeyl`, the
homomorphism law reduces the required equality to equality of these
permutations. The natural-value formula, the rank equations and the
finite-index bounds prove it in every branch. This proves

```text
blockWeyl hD hrD * append hr w_N * rightWeyl hr
  = w_R * blockWeyl h hr.
```

Here `w_n` denotes the existing unsigned `GeneralLinear.weylLong n K`.
In ordinary matrix notation this is
`diag(w_b,w_(c+a)) * diag(w_N,w_c)
 = w_R * diag(w_a,w_(c+b))`, the identity displayed on printed p.420.

Second, `reverseCoordinates` sends the five summands of the original
ordered coordinate type to the five summands in reverse order, reversing
each finite index. On the separating singleton it retains the unique
index. The lemma `coordinates_reverse` proves that this map, followed
by the specified reversed rank transport, is exactly `Fin.rev` on
the actual coordinates `Fin R`. Its proof uses the published coordinate
value formula, the total-rank equation and the five summands.

For `rectangleComparison`, equality of units reduces to equality of
their matrix entries. Both indices are expressed in the original ordered
coordinates. The existing long-Weyl conjugation formula reverses them,
inverse transpose swaps them and takes the inverse, and
`rectangleUnipotent_inv` negates both source rectangles. The lemma
`coordinates_reverse` now expresses the result in the reversed ordered
coordinates. The published `rectangleUnipotent_five_entry` on each side
reduces the comparison to the complete twenty-five-block entry table.
Case analysis and simplification give precisely

```text
x i l = -yD l.rev i.rev,
y i l = -xD l.rev i.rev.
```

Thus both negative signs arise from the actual inverse, both coordinate
reversals arise from the actual long-Weyl action, and the transpose
exchanges the source rectangles. The proof checks every remaining block
against its identity or zero entry as well.

Third, the inverse-transpose helpers show that this actual group
automorphism commutes with reindexing, block sums and `append`, and
fixes `blockWeyl` and `rightWeyl`. The first two follow by matrix
extensionality and the block entries; the remaining assertions follow
from the preceding block descriptions or the existing
`inverseTranspose_permutation`. The helper
`append_commutes_rightWeyl` proves that `diag(g,I_c)` commutes with
`diag(I_N,w_c)` through the block-sum homomorphism. The lemma
`append_reverse` identifies the inclusions with exchanged `j,k`
by their common entry formula, so their rank transports agree as
actual matrices.

In `fullComparison`, left multiplication of `rectangleComparison`
by `w_R` gives
`it_R(U_D) * w_R = w_R * U`, where `it_R` is inverse transpose.
The proof expands the existing `reversedMatrix` and `matrix`,
uses multiplicativity of inverse transpose, and applies its
involutivity to `Tg=w_N*it_N(g)`. After cancelling the adjacent
`w_R*w_R`, the left side is

```text
it_R(U_D) * blockWeyl hD hrD * append hr w_N
  * append hr g * rightWeyl hr.
```

Commuting `append hr g` past `rightWeyl hr` exposes the exact
three-Weyl product. Substituting `threeWeyl` and then the rectangle
identity gives
`w_R * U * blockWeyl h hr * append hr g`, the existing
`matrix h hr g x y`. The final `rightWeyl` factor is therefore used
in the calculation.

The final theorem introduces every quantified field, dimension, family
and rank proof from the unchanged closed proposition. It assembles
`threeWeyl`, `rectangleComparison` and `fullComparison` into its three
conjuncts. It assumes no positivity of `j,k` or of `m 0,m 1`.
When a rectangle dimension is zero, the corresponding finite summand
has no indices; the equivalence-based and entrywise proofs above
apply unchanged. They impose no nonempty-index or invertible-scalar
condition, and hold in every field, including characteristic two.

Worker 1197 implemented the Lean proof. Worker 1198 checked the
coordinate reversal and scope and authored this proof explanation.
This result proves the three pointwise matrix identities only. The
dual-section, scalar, measure, convergence and local-factor comparisons
remain separate obligations.
