# Strict block-length growth for concrete conjugate pair refinements

Author: Worker 328.

`Langlands.ConjugatePairRefinementRankStatement.{uF}` is a closed proposition
definition. It quantifies over every field `K : Type uF` with `[Infinite K]`
and every natural rank `n`. Its first conjunct states that for every supplied
`P Q : Langlands.Exponents.ConjugateBlockPair n K`,
`Q.StrictlyRefines P` implies `P.shape.length < Q.shape.length`. Its second
conjunct states `P.shape.length ≤ n` for every such `P`. Neither conjunct is
proved in this module.

The imported `ParabolicPair` construction supplies the actual matrix subgroups.
The hypothesis `Q.StrictlyRefines P` is exactly

```text
(Q.parabolic ≤ P.parabolic ∧ P.splitComponent ≤ Q.splitComponent) ∧
  ¬ (P.parabolic ≤ Q.parabolic ∧ Q.splitComponent ≤ P.splitComponent).
```

Here each parabolic is the conjugate upper block parabolic and each split
component is the range of the conjugated block-scalar homomorphism. Strictness
concerns these subgroups, so distinct presentations of the same pair do not
qualify. Both conjugating matrices are arbitrary. There is no standardness,
consecutive-refinement, permutation, distinct-block-size or positive-rank
premise. Repeated sizes and one-block shapes are included. At rank zero the
positive-size/sum conditions on `BlockShape` force an empty shape; the
universal quantifiers still include that rank.

The source is A. J. Silberger, *Introduction to harmonic analysis on reductive
p-adic groups* (Princeton University Press and University of Tokyo Press, 1979),
registered as `silberger-1979-harmonic-analysis`, retained SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Section 0.3, printed pp.5–6 (one-based PDF pp.11–12), was read in the original,
including both page images. Page 5 defines a parabolic pair and its p-rank as
the codimension of the split component of the ambient center in the pair's
split component. Page 6 orders pairs by parabolic inclusion and reverse
split-component inclusion and discusses conjugacy to standard pairs.

This proposition is a derived finite-dimensional type-A geometry target, not
a verbatim theorem of that section. For positive rank, a shape of length `k`
has split-component dimension `k` and the source's p-rank is `k - 1`. Strict
growth of block length therefore supplies the rank measure needed for the
source's pair-minimum argument. The bound comes from positive block sizes
summing to `n`. The asserted extension to every infinite field is algebraic:
it uses no topology, valuation or representation. In particular its quantifiers
permit direct specialization to the carrier of every supplied p-adic field.

The future proof must obtain the length comparison from the concrete subgroup
inclusions. A possible route uses the associated finite flags or the
finite-dimensional algebras of conjugated block-scalar matrices, including
an argument that equality of lengths under refinement forces equality of the
actual pairs. The existing injective group homomorphism `scalarInclusion`
alone does not establish a dimension inequality. The infinitude hypothesis is
explicit; the field-valued points of split components can lose information
over small finite fields (over `𝔽₂`, all unit coordinates are trivial).

No weakly critical support, tempered support or exhaustion, critical-to-minimal
converse, regular exhaustion, equal-exponent grouping or other
representation-theoretic result is assumed or established here. The separate
exact-target proof task must retain the full quantifiers and the imported
actual subgroup relation. Publication of this statement supplies a target,
not proof evidence for its consumers.
