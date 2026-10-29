# Proof of geometric unequal-rank support

Author: Worker 676.

`Langlands.RankinSelberg.unequalRankIwasawaSupport` proves the imported
`UnequalRankIwasawaSupportStatement F T n j k`, for every prime `p`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, and every
natural `n,j,k`. It adds no assumptions. For each `R > 0` it constructs one
compact set of actual `j` by `n+1` matrices before quantifying over `g,x`
and the Iwasawa factors.

The proposition and its source specialization are documented in
[UnequalRankIwasawaSupportStatement.md](UnequalRankIwasawaSupportStatement.md).
The source there is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions* (1983), §2.4(3), Lemma 2.6 and its proof,
and the unequal-rank application on printed p.393. This module supplies an
internal derived proof of the published geometric implication. Its algebraic
lemmas implement the argument below; they are not new assertions
about the source's full gauge lemma. The proof uses a direct factorization
of suffix minors, rather than proving invariance of a maximum of minors.

Put `r = n + (j+k+1)` and `M = unequalRankMatrix j k g x`. All absolute
values below mean `T.normalizedAbs`. The given factorization is
`M = u * diagonalUnits a * κ`, with the actual upper unipotent and
integral subgroups from the statement.

## Suffix minors and entry extraction

For a finite index `t`, the suffix index type is `{i : Fin (r+1) // t ≤ i}`.
For any upper triangular matrix `U` and arbitrary matrix `A`, restricting
the rows of `U*A` to this suffix and selecting any equally indexed columns
gives the product of the suffix square block of `U` with the selected
suffix rows of `A`. Terms outside the suffix vanish by upper triangularity.
Taking determinants therefore gives

```text
det ((U*A)[suffix,cols])
  = (product of U(i,i) over the suffix) * det (A[suffix,cols]).
```

The implementation proves the matrix equality by restricting its finite
sums and uses `Matrix.det_mul` and the triangular determinant formula.
It applies this identity to `U = u * diagonalUnits a` and `A = κ`.
Here `U` is upper triangular and `U(i,i)=a_i`. Every entry of `κ` is
in `T.Integers`, hence every selected determinant is integral as well:
the determinant is transported from the subring through its inclusion.
The published normalization theorem identifies integrality with
absolute value at most one. Multiplicativity then bounds each suffix
minor of `M` by the product of the `|a_i|` on that suffix.

For an entry `x(t,c)`, choose the suffix beginning at ambient row
`t' = n+1+t`. At its first index select ambient column `c`; at every
later index select the identity column with that ambient index.
The resulting square matrix is lower triangular. Its first diagonal
entry is exactly `x(t,c)` and every later diagonal entry is one.
Thus its determinant is exactly `x(t,c)`, with no sign ambiguity in
this indexing. The formulas are proved directly from
`unequalRankMatrix_val`, including the fact that the lower left
block contains `x` itself.

## Diagonal and uniform entry bounds

The final row of `M` is the final standard basis row. The final row
of `u * diagonalUnits a` is `a_r` times that same row. From
`M * κ⁻¹ = u * diagonalUnits a` it follows that
`a_r = (κ⁻¹)(r,r)`, so `|a_r| ≤ 1`. From the original factorization
one gets `1 = a_r * κ(r,r)`; since `|κ(r,r)| ≤ 1`, this gives
`1 ≤ |a_r|`. Both matrix and inverse integrality come from
`Conductor.mem_integralSubgroup`. Consequently `|a_r|=1`.

Set `B = max 1 R`. Reverse induction over `Fin (r+1)` uses the adjacent
ratio hypotheses and multiplicativity to give
`|a_i| ≤ B^(r-i) ≤ B^r`. This uses arbitrary field units; there is no
restriction to powers of a uniformizer. A suffix has at most `r+1`
indices, so its product of absolute diagonal entries is bounded by

```text
E = (B^r)^(r+1).
```

Product monotonicity uses nonnegativity of normalized absolute values,
and the comparison of powers uses `B^r ≥ 1`. Combining this estimate
with the selected minor identity gives `|x(t,c)| ≤ E` for every entry.
The deliberately coarse common bound depends only on `R,n,j,k`, and
is independent of `g,x,u,a,κ`.

## Compactness in the supplied topology

The compact-set helper uses the published equalities
`T.normalizedAbs z = F.canonicalNorm z ^ d` and
`T.topology =` the canonical norm topology, where
`d = Module.finrank (Padic p) F.Carrier > 0`. These are consequences
of the supplied `T`; no topology or normalization assumption is added.

Since `E ≥ 1`, a field element with `T.normalizedAbs z ≤ E` satisfies
`‖z‖^d ≤ E ≤ E^d`, and hence `‖z‖ ≤ E`. The canonical closed ball
of radius `E` about zero therefore contains every such element.
The canonical normed field is a finite dimensional normed space over
the locally compact field `Padic p`; `FiniteDimensional.proper`
makes this closed ball compact. Rewriting the topology equality
gives compactness for exactly `T.topology`.

The final set is the set of rectangular matrices whose entries all
belong to that compact field ball. Two applications of compactness
of products prove compactness in the matrix's product topology.
The entry bounds prove membership.

## Zero parameter cases

There is no positivity assumption on `n,j,k`, and the Lean proof uses
no separate positivity branch. For `j=0`, the product over rows is
empty, so this same compact matrix set is the singleton rectangular
space; its membership condition is vacuous. For `n=0` the rectangular
space still has one column and every formula applies. For `k=0` the
trailing identity block still has size one, so the standard final row
used to normalize `a_r` remains present. These arguments also cover
`n=j=k=0`. Values `0<R<1` are covered by replacing `R` with `max 1 R`
in the estimates while retaining the exact proposition's hypotheses.

The helpers `normalizedAbs_prod`, `diagonal_abs_last` and
`diagonal_abs_bound` are public for reuse by the weighted Whittaker square
reduction. Their statements and proofs are unchanged: they express finite-product
multiplicativity, the unit final Iwasawa coordinate, and the bound from adjacent
ratios, respectively.
