# Closed-immersion proof on actual scheme point spaces

Author: Worker 105. This proof is a relative and arbitrary-scheme extension of
the closed-immersion clause of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Proposition 3.1, printed page 4.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This unit implements `schemeClosedPointProperties_proof` for the exact target
`Langlands.AlgebraicGeometry.PointTopology.SchemePointClosedImmersionProperties`.
It uses the actual `RingPoint` carriers and explicitly named final topologies.
Localness, continuous multiplication and `IsOpenUnits` are the common
hypotheses. Hausdorffness of the value ring is used only for closedness of the
image. No finite-type or scheme-separation assumption is introduced.

## Actual restriction and image identities

`restrictedOver` constructs the actual restriction of a relative morphism to
an open of its target using Mathlib's `morphismRestrict`, proving its base
equation explicitly. `restrictedOver_fac` proves the actual square commutes.
`restrictedOverPoint_factor` gives the corresponding exact equality of point
maps under postcomposition.

`preimage_chart_subset_range` shows that points whose image factors through a
target chart factor through the actual inverse-image open of the source. The
proof uses whole scheme-image containment and the actual open-immersion lift;
it does not require a local value ring. `preimage_range_schemePointMap`
proves that the full point-map image, tested in a target chart, is precisely
the image of the restricted point map. Actual point-inclusion injectivity and
the preceding factorization identity prove both directions.

## Global embedding and closedness

For `isEmbedding_schemeClosedPointMap`, the target affine point charts are
open embeddings for the final point topology by `SchemeOpenPointProofs`.
Localness covers the target point set by these charts. A closed immersion is
affine, so the preimage of each affine target chart is affine. Its actual
restriction remains a closed immersion. The corresponding point map is an
embedding by the affine mapping proof; composing it with the target chart
inclusion is still an embedding. The source preimage-open point inclusion is
continuous, and `preimage_chart_subset_range` gives the required coverage of
each pulled-back chart. Mathlib's
`isEmbedding_of_iSup_eq_top_of_preimage_subset_range` applies these exact
local maps to conclude that the full actual point map is an embedding.

For `isClosedEmbedding_schemeClosedPointMap`, assume additionally
`T2Space S`. The restricted affine point maps have closed image by the affine
mapping result. `preimage_range_schemePointMap` identifies the inverse image
of the full range in every target chart with that restricted image. Their
complements are therefore open in every chart. The defining open-set criterion
of the final topology makes the complement of the full range open, hence the
range closed. Together with the embedding result this gives a closed embedding.

`schemeClosedPointProperties_proof` combines the embedding result and the
separately Hausdorff closed-embedding result into exactly the target. Its
explicit full binders preserve the target's quantifier order.

The unit imports the published affine mapping and open-chart proofs by their
Lean module names. The exact target covers actual scheme points under the
stated value-ring assumptions; other source assertions remain separate.
