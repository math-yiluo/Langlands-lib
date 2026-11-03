# Closed containment and centralizers of a dominant torus image

This internal helper compares actual group-scheme maps that differ by a scheme-theoretically dominant factor. It uses the Library's `SubgroupFunctor.range`, `torusCentralizer`, and `Dynamic.centralizer` interfaces.

Authors: Worker 1479 and Worker 1282. Worker 1479 proves the comparisons and constructs the closed factor; the product pullback and flat-base-change helpers reuse Worker 1282's published proof in `Rational.AffineCommutatorImageStability`.

`SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant` works over an arbitrary scheme. If `p : D ⟶ E` is schematically dominant, `i : E ⟶ G` is any homomorphism, and `b : B ⟶ G` is a closed subgroup, then the full range of `p ≫ i` lies in the range of `b` exactly when the full range of `i` does. The forward implication lifts the underlying map of `i` through the closed immersion using `exists_lift_of_isSchemeTheoreticallyDominant`; the map over the base then lifts each test point. The converse composes points with `p`.

`torusCentralizer_comp_eq_of_isSchemeTheoreticallyDominant` works over an arbitrary field and for commutative source group schemes `D` and `E`. If the underlying map of `p : D.toGrp ⟶ E.toGrp` is quasi-compact and schematically dominant and `G` is separated over the field, then `p ≫ i` and `i` have equal centralizer subgroup functors. The universal commutation test reduces this to equality of two morphisms on `U × E` for each test scheme `U`. The map `U × D ⟶ U × E` is the flat base change of `p`, hence schematically dominant. Every scheme over a field is flat, so this includes nonreduced test schemes. The separated-target dominance cancellation lemma proves equality. The converse pulls back the commutation equality.

For an actual `SplitTorusImage.DominantFactorization φ`, `range_le_iff` specializes closed containment, and `torusCentralizer_eq` specializes centralizer equality when the source is split and the target separated. Splitness makes the source and image affine, supplying quasi-compactness. Finally, `dynamicCentralizer_eq_torusCentralizer_image` identifies the published dynamic centralizer of every cocharacter with the torus centralizer of its dominant closed image.

`DominantFactorization.closedFactor d b hb hφ` constructs an actual group-scheme homomorphism from the image to any closed subgroup `b` containing the full range of `φ`. The equation `closedFactor_comp` identifies its composite with `b` as the image inclusion. The construction uses the published `factorHom` for the range represented by the closed immersion `b`, with containment supplied by `range_le_iff`. The theorem `isSplitSubtorus_closedFactor` shows that this factor is a closed split subtorus of the containing group, by the published closed-subgroup cancellation lemma and the original image's splitness.

The imported flat-base-change helpers supply the categorical pullback argument from the published `Rational.AffineCommutatorImageStability` module. The remaining proofs derive directly from the published closed-lift, dominance-cancellation, split-torus affineness, and universal-commutation lemmas. These statements retain arbitrary fields, universes, trivial and noninjective cocharacters, all test schemes, and arbitrary closed subgroups. They do not prove Borel maximality or `CentralizerBorelIntersectionStatement`.

The flat-base-change dominance step reuses the unchanged exported
`RelativeRoot.CommutatorCoordinates.whiskerLeft_schematic` helper from
`AffineCommutatorImageStability`; the duplicate local proofs are omitted.
