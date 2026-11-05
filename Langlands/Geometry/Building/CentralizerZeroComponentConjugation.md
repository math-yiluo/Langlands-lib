# Centralizer-zero conjugation by the zero-component normalizer

This is an internal derived intermediate construction for the actual
`ParahoricBuildingData P`, at arbitrary field universe. The normalization results
retain `P.zeroDatum.CoverImageCentralizerNormKernelStatement` as the explicit
cover comparison. They establish normality of the actual centralizer-zero
subgroup inside `N(F) ∩ G(F)^0`. Normality in the full normalizer and the closing
affine Iwahori–Tits statement remain separate obligations.

The first theorem has no cover-comparison premise. The published product
decomposition of the actual zero subgroup writes a point `n` of
`P.normalizerZeroComponent` as `c * j(z)`, with `c` in the simply connected image
and `z` in `P.centralizerZero`. Since `n` and `j(z)` both belong to the actual
normalizer, `c = n * j(z)⁻¹` belongs to it too. This yields a product equality in
the original normalizer group, together with its converse.

Under the cover comparison, the simply connected normalizer factor normalizes
the full mapped centralizer-zero subgroup by
`CentralizerZeroSCNormalizerConjugation`. The factor `j(z)` lies in that subgroup,
so it also normalizes it. Their product therefore normalizes the subgroup.
The normalizer membership criterion gives the stated forward conjugation
membership theorem.

The published `mem_normalizerZero_iff` transfers this normalization to
`P.normalizerZero` inside the actual normalizer group. The standard subgroup
criterion then proves
`(P.normalizerZero.subgroupOf P.normalizerZeroComponent).Normal`.

`centralizerZeroComponentNormalizerAut` restricts actual ambient conjugation
to the mapped centralizer-zero subgroup. Its coercion theorem states that its
underlying rational-point value is exactly `n * g * n⁻¹`.

The provenance is internal deduction from the published actual zero-subgroup
product decomposition and the conditional simply connected normalizer
conjugation result. No new literature assertion, apartment axiom, factor-pair
existence premise, or global normality premise is introduced.
