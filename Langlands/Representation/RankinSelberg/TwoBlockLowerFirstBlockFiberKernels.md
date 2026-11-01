# Actual lower mixed quotient fiber kernels

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels`.
Author: Worker 1196.

This module constructs the two measurable kernels required by the published
`TwoBlockLowerFirstBlockQuotientIntegrationStatement`, using the existing actual
lower mixed subgroup and the published fiber maps. This is derived support for
JPSS (1983), Section 4.9, equations (2) and (8), printed pages 416 and 418;
the source is registered as `jpss-1983-rankin-selberg`. The scan's formulas and
the lower subgroup definition motivate the kernels. Measurable measure-valued
descent is internal measure-theoretic packaging, not a claim quoted from JPSS.

Every prime, canonical p-adic field universe, positive pair of block ranks,
and rank equality is retained. The field and quotient measurable structures
are canonical Borel structures. The rectangle retains its product measurable
structure; second countability supplies its Borel instance.

For each supplied rectangular additive Haar measure `muR`, `radicalKernel` is
a kernel from the actual lower mixed quotient `Lminus \ G` to the actual
mixed quotient `M \ G`. `radicalKernel_mk` proves the everywhere formula

```text
radicalKernel muR [g] = map (Z ↦ radicalFiberPoint Z g) muR.
```

Joint continuity of the published fiber map gives measurability of the
representative measures via the Giry map and product map. The published
`measurePreserving_radicalChange` preserves the supplied `muR` under
`Z ↦ n⁻¹ (Z + Z0) a0`. The representative-change formula therefore makes
the measure-valued map invariant under left multiplication from `Lminus`.
`measurable_quotient_iff` then descends it measurably through the closed
subgroup quotient. No rectangular normalization or scalar is inserted.

For any s-finite measure `nuA` on the actual small unipotent quotient and
any proof of the published `NormOneRightInvariant` property, `firstBlockKernel`
is the kernel from `Lminus \ G` to `Hminus \ G` with everywhere formula

```text
firstBlockKernel nuA k [g] =
  map (q ↦ firstBlockFiberPoint q g) (nuA restricted to AQk).
```

Joint continuity again gives measurable representative measures. The actual
lower mixed representative change is right translation of `q` by `a0`.
The published `map_restrict_smallSlice` preserves the supplied small measure
on every integer slice, using norm-one right invariance and the determinant
order zero of `a0`. This gives descent through the same closed subgroup.
The kernel remains the unweighted slice pushforward.

These results establish measurability and representative formulas. They do
not assert s-finiteness of the resulting kernels, measure existence,
normalization, compatible quotient integration, either disintegration,
or convergence of any representation-specific integrand. In particular,
they do not remove the cube factor in equation (2) or the positive density
in equation (8); those belong to subsequent measure identities.
