# Connectedness of smooth closed subgroups containing a Borel subgroup

Lean module `Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected`.

## Theorem

`Langlands.GroupScheme.borelContainingSubgroupConnectedStatement` proves the published
statement `BorelContainingSubgroupConnectedStatement.{u}` from
[BorelContainingSubgroupConnectedStatement](BorelContainingSubgroupConnectedStatement.md).
This is the connectedness clause of Milne, *Algebraic Groups* (2017), Corollary 17.49.
Let `k : Type u` be an algebraically closed field and `G` a smooth affine group scheme over
`k` with connected underlying space. Let `i : P ⟶ G` be a closed subgroup with `P` smooth,
`j : B ⟶ G` a Borel subgroup and `f : B ⟶ P` with `f ≫ i = j`. Then the underlying space
of `P` is connected.

The theorem has no hypotheses beyond the statement itself.

## Proof

The proof is one application of the reduction
`BorelContainingSubgroupConnected.borelContainingSubgroupConnected_of` from
[BorelContainingSubgroupConnectedReduction](BorelContainingSubgroupConnectedReduction.md).
That reduction derives the target from two hypotheses, and both are supplied by
published theorems:

- `BorelConjugacyStatement.{u}`: `Langlands.GroupScheme.borelConjugacy` from
  [BorelConjugacyProof](BorelConjugacyProof.md) (existence and conjugacy of Borel
  subgroups, cited in the statement's docstring as Milne 17.9(b));
- `BorelNormalizerStatement.{u}`: `Langlands.GroupScheme.borelNormalizer` from
  [BorelNormalizerProof](BorelNormalizerProof.md) (a Borel subgroup is its own
  normalizer on `k`-points, Milne 17.48).

The reduction's Markdown describes the argument: every `k`-point of `P` lies in the
identity component `P⁰`, and a Jacobson-space argument then shows that `P` is connected.
