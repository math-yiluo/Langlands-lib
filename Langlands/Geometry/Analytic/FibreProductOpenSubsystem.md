# Open factor patches in a fibre-product chart gluing

This internal topology construction applies the open subsystem criterion to
the actual `FibreProduct.chartSystem`. The two factor atlases are assumed to
contain all local domains. The factor patches are open. There are no global
Hausdorff or finite-overlap hypotheses.

`IndexedAffinoidAtlas.exists_subchart_neighborhood` uses the existing actual
rational-neighborhood theorem in an original chart spectrum. Domain saturation
gives an original chart with exactly that rational domain's ambient image.
Injectivity of the original chart identifies its preimage with the rational
locus, preserving both the neighborhood property and subordination.

`patchPairs f g U V` selects pairs with first chart range contained in `U` and
second chart range contained in `V`. Componentwise chart inclusion makes this
selection downward closed. For a point of any original pair spectrum above
`U` and `V`, the preceding lemma supplies smaller factor charts around its two
projections. Their common base chart is inherited from the original pair.
The actual pair restriction image is the intersection of the two inverse-image
factor chart ranges, so continuity of the two bounded spectrum maps makes it
a neighborhood of the original point.

`subsystemSupport_patchPairs` identifies the selected support with
`fst ⁻¹' U ∩ snd ⁻¹' V`. The reverse containment uses the neighborhood pair
and its actual restriction map; it does not use any lifting theorem for
ordinary point pairs. Continuity of the two projections proves chartwise
openness of this support. In each actual support preimage the constructed
pair chart still gives a neighborhood. Its singleton range is the finite
quasinet witness in `hasLocalSubchartCover_patchPairs`.

`isOpenEmbedding_patchSubsystem` now applies the open subsystem theorem.
The source is the quotient gluing of the selected original pair algebras,
and its image is exactly the displayed open inverse-image patch. This proves
only the stated topology comparison. It does not yet establish local
Hausdorffness, construct a small analytic pullback presentation, or prove a
categorical universal property or etale base change.

All results are derived from the published rational-neighborhood and
fibre-product chart-system constructions and the companion chart-subsystem
helper; no external literature assertion is transcribed.
