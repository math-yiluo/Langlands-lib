# Permutation standardization of a semistandard GL block pair

`Langlands.GLSemistandardStandardizationStatement.{uF}` is a proposition
about the actual matrix subgroups attached to a conjugated block pair.
It quantifies over every prime `p`, every `PadicField.{uF} p`, every rank
`n`, and every `ConjugateBlockPair n F.Carrier` named `P`.

Write `B = P.shape` and `c = P.conjugator`. The sole geometric hypothesis is
that `P.splitComponent` is contained in the split component of the standard
singleton-block pair. By the definitions in `ParabolicPair`, the former is
the range of `a ↦ c * B.blockScalar F.Carrier a * c⁻¹`. The latter is the
subgroup of invertible coordinate diagonal matrices, as described by
`SingletonBlocks`. These are actual subgroups of `GL_n(F)`.

The conclusion supplies a permutation `w` of `Fin n` and an actual element
`m` of the product Levi `B.Levi F.Carrier` satisfying

```text
GeneralLinear.permutation n F.Carrier w * c = B.leviEmbedding F.Carrier m.
```

The ordered shape is unchanged: the row permutation makes `c` block diagonal
in precisely the original ordered blocks. No representative, subgroup identity,
representation-theoretic premise, or standardization witness is assumed.
The statement includes rank zero and the one-block case. It requires no
choice of topology, chamber, or exponent, and preserves the independent field
universe `uF`.

This is a derived elementary matrix statement, not a verbatim assertion from
an external source. Its mathematical rationale is that the block-scalar torus
has distinct block characters over the infinite p-adic field. If its conjugate
is diagonal, its simultaneous eigenspaces are sums of coordinate lines. Each
such eigenspace has its original block dimension. Ordering these coordinate
lines block by block gives the required row permutation; invertibility then
gives an invertible matrix on each block. This rationale describes the intended
result, not an implemented proof. The Lean file contains only the Prop-valued
definition. An exact proof requires a separate contribution.

This interface serves the semistandard conjugacy proof and existing geometry
task `926567c9-a739-4eec-8a22-6f9c2b21ebf0`. It imports only the block-pair,
singleton-block, and permutation definitions, so it does not depend on any
Langlands classification statement. In particular, it is not a conditional
replacement for the final conjugacy theorem.
