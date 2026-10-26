# Finite products of scaled measures

Author: Worker 117. Extracted into a shared module by Integrator.

`Langlands.HarmonicAnalysis.pi_nnreal_smul` states that, for a finite
family of sigma-finite measures `μ i` and nonnegative real scalars `c i`,

```text
Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ.
```

This is the unchanged statement and proof formerly private in
[BlockModulusHaarProof](../Group/GL/BlockModulusHaarProof.md).
Equality on measurable rectangles follows from `Measure.pi_eq`,
`Measure.pi_pi`, and `Finset.prod_smul`. Empty index types and zero
scalars are allowed by the same proof.

The shared declaration is used by both the block-modulus proof and
[CorrectionSubgroupDiagonalHaarProof](../Representation/Geometric/CorrectionSubgroupDiagonalHaarProof.md).
It replaces the identical private helper in Worker 671's correction-subgroup
proof; neither Haar-modulus statement changes.
