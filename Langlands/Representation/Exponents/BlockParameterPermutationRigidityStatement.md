# Ordered block parameters determined by permuted diagonal coordinates

`Langlands.Exponents.BlockParameterPermutationRigidityStatement` is a closed
proposition definition. It states an internal finite-order and counting lemma;
this module supplies no proof.

For every natural number `n`, let `B` and `C` be the existing
`Langlands.GeneralLinear.BlockShape n`, and let
`t : Fin B.length → ℝ` and `s : Fin C.length → ℝ` be strictly decreasing.
Suppose there exists a permutation `w : Equiv.Perm (Fin n)` such that, for
every actual diagonal coordinate `a`,

```text
t (Langlands.Geometric.blockIndex B a) =
  s (Langlands.Geometric.blockIndex C (w a)).
```

The conclusion is the existence of an order isomorphism
`b : Fin B.length ≃o Fin C.length` for which every block index `i` satisfies
both

```text
B.size i = C.size (b i)
t i = s (b i).
```

Thus the ordered block sizes and parameter values are recovered together.
Neither equality of the block lengths nor a preliminary block matching is an
assumption. The coordinate permutation need not be assumed to preserve either
block partition: the correspondence of its block fibers is to be deduced.

The functions are determinant exponents repeated once per diagonal coordinate.
Block `i` contributes `B.size i` copies of `t i`; the displayed coordinate
equality does not use the scalar-center exponent `B.size i * t i`.
There is no zero-sum or sign condition on the parameters. Every common real
shift of `t` and `s` remains allowed. Strict decrease is vacuous for a one-block
shape, so that case is included. Rank zero is also included: positivity of all
block sizes and their sum being zero force both block index sets to be empty.

## Proposed elementary proof route

Positivity of `B.size i` supplies a coordinate `B.index i j` in each source
block. Apply `w` to such a coordinate and take its `C` block index. The
coordinate equality gives a target index with value `t i`. Injectivity of
the strictly decreasing function `s` makes this target index independent of
the selected coordinate. This defines a map `b` between block indices with
`t i = s (b i)`.

Repeat this construction with `w.symm`, exchanging `B,t` and `C,s`.
Injectivity of `t` and `s` makes the two block maps inverse. In particular,
the coordinate permutation sends the entire fiber of `blockIndex B` at `i`
bijectively onto the fiber of `blockIndex C` at `b i`.
The existing `BlockShape.indexEquiv` and `Geometric.blockIndex_index` identify
these fibers with `Fin (B.size i)` and `Fin (C.size (b i))`. Equality of
their finite cardinalities gives equality of the block sizes.

Finally, strict decrease and the preserved values give, for all `i,j`,

```text
i ≤ j ↔ t j ≤ t i ↔ s (b j) ≤ s (b i) ↔ b i ≤ b j.
```

The block bijection therefore upgrades to the required order isomorphism.
This route uses no coordinate choice when there are no block indices and
covers the empty case as well. It is a proposed route for a separate proof,
not an implemented proof in this statement module.

## Internal provenance and scope

The statement and the proof route above are internally derived finite
combinatorics. They are motivated by the last standard-chamber rigidity step
in A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
Proposition 6.1, printed pp.102–103, especially the conclusion from regular
positive-chamber parameters on p.103. Those pages were read, including the
formulas in the p.103 page image. The exact finite-coordinate assertion here
is not stated verbatim in that source.

Motivating source ID:
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`.
Original PDF SHA-256:
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.

The assumed coordinate equality is an elementary input. This module supplies
no representation-theoretic Weyl comparison, cuspidal-support conjugacy,
analytic continuation, tempered cone bound, head theorem, Langlands quotient
uniqueness, or square-integrable classification. Its imports provide the
existing block coordinates and the real numbers; none of those downstream
classification results is used.
