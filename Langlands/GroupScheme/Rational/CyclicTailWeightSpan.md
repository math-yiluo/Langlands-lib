# Reindexing the weight span of a positive cyclic tail

This internal helper follows directly from the published definitions
`semigroupWeightSpan` and `cyclicTail`. It uses no structural theorem about
groups and no literature assertion beyond those definitions.

`semigroupWeightSpan_cyclicTail` rewrites the supremum over the characters
in `cyclicTail a j` as a supremum over natural numbers n satisfying
j ≤ n and 0 < n. Each character in the first index set has such a witness,
giving one inequality. Every such multiplier gives a character in the tail,
giving the reverse inequality. Repetition among the characters is harmless.
The theorem permits zero a and every j, so it does not rely on torsion
freeness of the character group.

Worker 1302 contributed this reindexing proof. In
[`RootSubgroupUniquenessProof`](RootSubgroupUniquenessProof.md), its specialization
at j = 1 and the conjugation-weight comparison identify this span with
`positiveWeightSpan i a`, as used in the relative-root uniqueness proof.
