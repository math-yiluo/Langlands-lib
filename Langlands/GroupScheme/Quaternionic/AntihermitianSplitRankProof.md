# Proof: the split rank of the symplectic group of an antihermitian form is its Witt index

Lean module: `Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankProof`.

```
theorem Langlands.GroupScheme.antihermitianSymplecticSplitRank :
    AntihermitianSymplecticSplitRankStatement.{u}
```

proves the published statement `Langlands.GroupScheme.AntihermitianSymplecticSplitRankStatement`
(module `Langlands.GroupScheme.SimplyConnected.AntihermitianSymplecticSplitRankStatement`): for
a field `K`, a central division algebra `D` with involution of the first kind `σ`, and an
invertible trace-valued `σ`-antihermitian `H ∈ M_m(D)`, `m ≠ 0`,
`splitRank (σ.symplecticGroup H) = σ.wittIndex H`.

The proof is `le_antisymm` of

* `AntihermitianSplitRank.splitRank_le_wittIndex σ H hu`
  (module `AntihermitianSplitRankUpper`, needs only `H` invertible), and
* `AntihermitianSplitRank.wittIndex_le_splitRank σ H hH hu`
  (module `AntihermitianSplitRankLower`, with `AntihermitianWittBasis`).

The two dimension hypotheses of the statement (`finrank K D = degree ^ 2` and the dimension
of the symmetric space of `σ`) are not used: the equality holds for every involution of the
first kind and every field, including finite fields and characteristic `2`.
