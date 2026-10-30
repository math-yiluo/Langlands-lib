# Root/weight cone decomposition for GL block parabolics

Author: Worker 19.

`Langlands.GLParabolicRootWeightConeStatement` is a derived coordinate
specialization of Silberger 1978, Lemma 7.1. It states the unique standard
parabolic coarsening associated to a real exponent vector, including its
central component. It is a proposition definition, not a proof. The
published theorem `glParabolicRootWeightCone` proves it; see the last
section.

## Statement over actual block shapes

Fix a positive rank `n` and an actual `GeneralLinear.BlockShape n`, with
positive block sizes `n_i`. Let `r_i` be arbitrary real numbers in
block-scalar exponent coordinates. Thus a real character has the form
`product |a_i|^(r_i)` on scalar matrices in the blocks. If its determinant
exponents are `v_i`, then `r_i = n_i v_i`.

There is a unique coarser positive ordered block shape `C` for which there
are a monotone surjection `q` from the original block indices to the new
ones and real numbers `t_j` satisfying:

1. Each new size is the sum of the old sizes in its fiber.
2. The `t_j` are strictly decreasing.
3. On each fiber, `sum r_i = (C.size j) t_j`. Hence `t_j` is its weighted
   average determinant exponent.
4. Every initial segment of a fiber has
   `sum (r_i - n_i t_j) ≤ 0`.
5. Over every commutative ring, the actual upper block parabolic of `B`
   is contained in that of `C`, and the actual embedded Levi of `B` is
   contained in that of `C`.

Monotonicity and surjectivity make the nonempty fibers consecutive runs.
The rank equations identify their actual standard block positions.
The partial-sum clause includes the last member of each run, where the
preceding average equation makes the sum zero.

The `∃!` quantifier asserts uniqueness of `C`. The grouping map and exponents
are existential witnesses; the Lean statement does not separately assert
their uniqueness. It assumes neither a chosen coarsening nor a cone
decomposition. Positive rank avoids an empty ambient group. For a single
block the result has one block and strict decrease is vacuous.

## Derivation from the original cone lemma

The retained original is Allan J. Silberger, *The Langlands quotient theorem
for p-adic groups*, Math. Ann. 236 (1978), 95–104, §1 p.96 and the preparation
and statement of Lemma 7.1, p.103. Proposition 7.2, pp.103–104, explains its
role in exhaustion. Literature ID
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
retained PDF SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
PDF page 1 is printed p.95. The article was read in full, and the
formula-bearing page 103 was checked in its page image.

The following coordinate calculation is a derived specialization; the
source does not print the statement in this form.

Write `N_j = n_1 + ... + n_j` and use on the scalar-coordinate real dual
the positive inner product

```
<x,y> = sum_i x_i y_i / n_i.
```

This is the inner product induced from the standard Weyl-invariant
Euclidean form on the full diagonal torus. The projected simple root at
the boundary after block `j` is

```
alpha_j = e_j - e_(j+1).
```

Its dual weight has scalar coordinates

```
(lambda_j)_i = n_i (1_(i ≤ j) - N_j / n).
```

These roots and weights lie in the central orthogonal complement
`sum x_i = 0`. Directly, `<alpha_i,lambda_j>` is the Kronecker delta.
Adjacent distinct roots have inner product `-1/n_(i+1)`; nonadjacent
ones have inner product zero. Thus they meet the exact hypotheses of the
published abstract `RootWeightConeDecompositionStatement`.

First remove the central component: put `c = (sum r_i)/n` and
`r_i^0 = r_i - n_i c`. Silberger's lemma gives a unique subset `F` of
boundaries and

```
r^0 = sum_(j in F) c_j lambda_j - sum_(j not in F) d_j alpha_j,
c_j > 0,  d_j ≥ 0.
```

The determinant-coordinate vector of the positive-weight term is constant
between boundaries in `F`, and its drop at a boundary in `F` is exactly
`c_j`. After restoring the common central scalar `c`, these constants are
the strictly decreasing `t_j` on the runs that form `C`.

Set the absent root coefficients at boundaries in `F` to zero. On a run,
the partial sum of `r_i - n_i t_j` through an internal boundary `k`
is `-d_k`, hence is nonpositive. At the end of a run it is zero.
This gives both the average and residual clauses of the Lean statement.
Conversely, the residual clauses reconstruct the nonnegative `d_k`, and
the strict drops reconstruct the positive `c_j`. Thus any proposed
coarsening determines precisely the support `F` in the original lemma.
Its uniqueness gives uniqueness of the coarsening. Equal adjacent average
exponents must be merged; allowing weak decrease would lose this conclusion.

The subgroup containments are the corresponding elementary matrix
consequences. A fine upper block-triangular matrix is upper triangular
after merging consecutive blocks. A fine block-diagonal matrix is diagonal
for the same coarser blocks. These use the existing `BlockShape` matrix
constructions, not abstract groups or supplied containment witnesses.

## Scope and remaining proofs

The central direction is unrestricted. This extends the source's
central-orthogonal formulation by subtracting and restoring its central
projection; it does not discard unramified central twists.
The sign of the residual is the minus sign on the root-cone term in
Silberger's lemma. The averaged determinant exponents decrease for upper
parabolics, consistently with the positive character `q^(<lambda,H>)`.
No statement about induction or Jacquet normalization is added here.

The field-free numerical specialization and subgroup containments apply to
the actual block parabolics over every commutative ring; the representation
theory consuming them remains over finite extensions of `Q_p`.
The ring universe is arbitrary. No representation carrier universe occurs.

The coordinate statement is proved. `Langlands.glParabolicRootWeightCone`
(module `Langlands.Representation.Classification.ParabolicConeProof`) proves
`GLParabolicRootWeightConeStatement.{uR}`. It combines three proved
statements of `ParabolicConeAuxiliaryStatement`:

- `glBlockConeExists` proves numerical existence by pooling adjacent blocks
  until the averages strictly decrease;
- `glBlockConeUnique` proves uniqueness of the coarser shape by summation by
  parts;
- `glBlockCoarseningSubgroups` proves the parabolic and Levi containments
  over every commutative ring.

This proof does not use the derivation from Silberger's lemma given above
and does not use the abstract `RootWeightConeDecompositionStatement`. That
abstract lemma is still unproved in the Library.

This family supplies the parabolic cone target. It does not assert that a
vector is a Jacquet exponent, choose a maximal exponent of an irreducible
representation, prove temperedness of any Levi representation, or give the
maximal-cone argument in Proposition 7.2. The Library treats that selection
separately. `GLMaximalConeJacquetQuotientStatement` (module
`MaximalConeStatement`) is a corrected dominance form of it, and
`glMaximalConeJacquetQuotient` proves it using `glBlockConeExists`.
