# Restriction of the actual rank-one locus

This is an internal continuation of `Picard.LineBundleLocus`.
`imageOpenTrivialization` transports an actual trivialization on an open
of the source of an open immersion to its image open. Its proof uses
the inverse of `Scheme.Hom.isoImage`, the restriction composition and
congruence comparisons, and `restrictUnitIso`.

`rankOneLocus_restrict` proves equality of the rank-one locus of a
restriction with the inverse image of the original rank-one locus,
for every open immersion of arbitrary `Scheme.{u}`. The forward
direction extends a local trivialization to its image open using the
displayed construction. The reverse direction uses the already
constructed forward pullback containment and the restriction/pullback
comparison. Neither direction requires quasi-coherence, finite
presentation or flatness.

It follows that `M.restrict U.ι` is locally free of rank one if and
only if `U` is contained in `rankOneLocus M`. Together with the
full-fibre property from `LineBundleLocus`, this proves that an open
`V` of the base lies in `rankOneBaseOpen f M` if and only if `M` is a
line bundle on the full inverse image of `V`.
`lineBundleOverBaseOpenOfLE` constructs this actual line bundle.
Universal closedness of `f` suffices; proper morphisms supply it.

The provenance is the local trivialization definition already
implemented in `Picard.LineBundle` and the explicit elementary
construction of `Picard.LineBundleLocus`. The proper-image step is
motivated by Stacks Project, Lemma 99.10.1,
[Tag 0D03](https://stacks.math.columbia.edu/tag/0D03).
Registered source: `stacks-picard-stack-algebraicity-2026-11-01`,
SHA-256
`f152eeac350ef0fb061c6651f63b2a7cdeb5d175ad92aacbf99e5e9f6eb0b0e0`,
retained file `0D03.txt`, proof of Lemma 99.10.1.
These comparisons for open immersions are internal consequences of
the actual local-trivialization convention.

The converse in this file concerns open immersions. The full converse
under arbitrary scheme base change for finitely presented relatively
flat coherent families, and the Picard-stack atlas theorem, remain
separate proof obligations.
