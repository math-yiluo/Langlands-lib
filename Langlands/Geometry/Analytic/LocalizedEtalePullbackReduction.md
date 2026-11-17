# Exact strong-map reduction for localized étale pullbacks

Author: Worker 250.

This internal reduction restates the original localized étale pullback
existence problem in terms of complete strong maps and source refinement.
The reduction is an equivalence. It supplies no proof of the remaining
geometric existence statement.

The coefficient field universe `u` and space universe `v` are independent.
All objects of the existence statements have space and atlas-index universe
`v`. The preliminary reflection theorem allows an independent atlas-index
universe `w`. There are no Hausdorff or compactness assumptions.

`isRefinedStrongPullback_of_isPullback` reflects an actual localized
pullback square whose four maps are mapped strong maps. Localization
faithfulness reflects its commutativity and joint uniqueness. A localized
lift of a strong cone is represented by a full right fraction. Its
denominator is the required source refinement, and faithfulness reflects
the two projection equations of its numerator. Together with descent,
`isRefinedStrongPullback_iff_isPullback` identifies the two universal
properties for a mapped square.

`RefinedStrongEtalePullbackStatement K` asks that each strong cospan with a
strong étale first arrow admit a strong square satisfying
`IsRefinedStrongPullback`, with a strong étale second projection. The
universal property includes complete bounded algebra maps and allows a
full quasi-isomorphism source refinement for existence.

`exists_refinedStrongPullback_of_localized` puts the two projections of an
actual localized pullback of mapped strong arrows on a common strong
source. The common denominator is a full quasi-isomorphism and becomes
an isomorphism. Transport of the localized pullback along this isomorphism
gives a mapped strong pullback square; reflection supplies its refined
strong universal property. Étaleness of the second projection transports
by composition with the denominator isomorphism and is reflected by the
published comparison with `strongEtale`.

`localizedEtalePullbackStatement_of_refinedStrong` treats arbitrary
localized cospans. Each arrow is an actual right fraction. Composing the
étale first arrow with its denominator isomorphism shows that its strong
numerator is étale. Apply the strong existence hypothesis to the two
numerators. Descent gives their localized pullback; transport along the
two denominator isomorphisms gives the pullback of the original arrows.
The second projection is the mapped strong projection followed by the
second denominator, hence is étale by composition.

`refinedStrongEtalePullbackStatement_iff` combines the two directions. The
remaining strong geometric construction therefore suffices for, and
follows from, the exact Library target
`LocalizedEtalePullbackStatement`. No new assumptions enter that target.

The provenance is an internal categorical deduction from the published
Ore right-fraction calculus, strong-source separation, localized étale
composition and numerator comparison. It transcribes no external source.
