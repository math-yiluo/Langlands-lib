# Coarse scalar character of a nested fine twist

Authors: Worker 526 wrote the draft; Worker 359 supplied the
effective-parameter and fibre-sum design calculation; Worker 252 checked and
submitted it.

`Langlands.Exponents.CoarseFineTwistScalarCharacterStatement.{uF,uV}` is an
internal Prop-valued definition. This module states a character interface;
it supplies no proof. The field and representation-carrier universes are
independent.

Fix a prime, a p-adic field `F` and its supplied topological realization `T`.
For a coarse shape `B`, a refinement `Q`, a refinement `R` of `B.flatten Q`,
and a direct refinement `S` of `B`, the literal equality
`h : (B.flatten Q).flatten R = B.flatten S` identifies the two fine shapes.
The fine representation `ω` is irreducible, admissible for `T.topology` and
unitarizable. The fine vector `v₀` satisfies the existing weighted
`IsPositiveRootParameter (B.flatten Q) R v₀` condition. Equality transport
gives `ωB` and `vB` on `B.flatten S`.

For every real coarse vector `t`, the conclusion constructs an actual
complex-unit character `χ` of `Fin B.length → F.Carrierˣ`. Its kernel is open
in the product unit-group topology. It acts by scalars on every vector of
the actual `RelativeJacquetMultiplicity.fineTwist T B S ωB vB t` along the
following specified map. Repeat a coarse tuple on all fine blocks inside
its coarse block, giving the fine tuple
`fun k => a (((B.flattenBlockEquiv S).symm k).1)`; apply the fine shape's
`blockScalarLevi`, then apply `Geometric.flattenedLeviEquiv F.Carrier B S`.
The forward equivalence is part of the action equation; no replacement group
or carrier is chosen. The fine twist itself is the published one, with fine
determinant exponent `-vB k + t (((B.flattenBlockEquiv S).symm k).1)`.

The real part of `χ` is exactly `fun i => (B.size i : ℝ) * t i`, in the
existing `T.IsRealPartOf` convention:

```text
‖χ(a)‖ = ∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((B.size i : ℝ) * t i).
```

The factor is the coarse block size: on each fine block of size `d_k` inside
coarse block `i`, the repeated scalar has determinant `a i ^ d_k`; these
sizes sum to `B.size i`, and the `vB` contributions cancel by the zero sums
described below. The unitary central part contributes norm one. There is no ordering, positivity or nonvanishing assumption on `t`. Every
rank is included, with no positive-rank assumption: at rank zero there are
no blocks and the coarse tuple group is trivial. One-block shapes need no
extra hypothesis either; for a middle block with a single fine block, the
adjacent-root sum in `IsPositiveRootParameter` is empty, so that fine
coordinate of `v₀` is zero. The statement has no middle quotient, coarse
tempered input, outer quotient, cuspidal-support or analytic hypothesis.

The provenance is an internal algebraic adapter for published definitions.
The intended derivation reuses `unitaryFineTwistScalarCharacter` with the
effective fine parameter `vB - t ∘ flattenOuter`: its zero-coarse fine twist
has the same exponent `-vB + t ∘ flattenOuter` as the required fine twist.
Restrict the resulting character along tuple repetition.
`PadicField.TopologicalData.isRealPartOf_coarsen` sums fine real coordinates
over each coarse fibre. The transported coarse-coordinate zero sums in
`positiveRootBlockSums` remove the contribution of `vB`. Reindexing by
`(S i).indexEquiv` identifies those coordinate sums with size-weighted fine
sums; the fine sizes sum to `B.size i`. Continuity of tuple repetition
preserves the open kernel. These named ingredients motivate the interface;
their assembly remains a separate proof obligation.

This character statement establishes no Jacquet occurrence, generalized
block decomposition, surjectivity on a block, opposite-Jacquet
compatibility, geometric identity layer, exponent exclusion, Hom
factorization, dimension bound or classification result.
