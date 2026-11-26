# Regrouping finitely supported sums over nested subgroups

For subgroups `L ⊆ M ⊆ N` of a group, multiplication of a chosen representative of an inner
coset in `L \ M` by a chosen representative of an outer coset in `M \ N` gives a bijection from
the pairs of cosets to `L \ N`. Projection to `M \ N` recovers the outer coset. Multiplying by
the inverse of its chosen representative recovers the inner coset.

`tsum_nestedCosets` applies this bijection to the product of a left `L`-invariant function and a
left `M`-invariant function, the latter evaluated at the outer representative. A finite set of
supporting outer cosets and finite support in each corresponding inner sum give finite support
after regrouping. The lemma uses the invariances to identify the values under reindexing.

`nestedCosetsEmbedding` includes relative cosets in the ambient coset space, and
`nestedCosetsEquivOfTop` gives the equivalence when the upper subgroup is the whole group.
`nestedCosetsEmbedding_out` compares representative evaluations for invariant functions.
`tsum_nestedCosets_mul_right` expresses invariance of the sum under the permutation induced by
right multiplication in the upper subgroup.

## Source

The application is the combination of the two rational coset sums in J. Arthur, *An introduction
to the trace formula* (2005), §13, proof of Proposition 13.3, printed p. 74, PDF p. 86. The coset
lemmas formalize the group-theoretic argument independently of the parabolic data. Literature ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
