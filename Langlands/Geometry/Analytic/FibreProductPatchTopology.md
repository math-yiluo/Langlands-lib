# Hausdorff patches in the fibre-product gluing

This internal construction restricts the original fibre-product chart system
and its actual bounded restrictions to factor charts contained in specified
subspaces. The field, space and index universes remain independent.

`patchSystem` is the downward-closed subsystem `patchPairs`, and `patchMap`
is its natural injective continuous map to the unrestricted quotient. The
chart formula retains the original pair-chart representatives.

`hasFiniteOverlaps_patchSystem` requires only that the two factor subspaces
be Hausdorff. For two selected pair charts, cover their first-factor and
second-factor intersections by finitely many original charts using compact
intersection inside each Hausdorff subspace. Pair these charts, using the
first pair's original common base as witness. The resulting pairs are
subcharts of both original pairs and remain selected by downward closure.
The actual restriction-image theorem lifts each gluing equality through
one of this finite set, and injectivity of the second quotient chart
identifies the second restriction image. The existing chart-system theorem
therefore gives `isClosedEmbedding_patchChart`.

No openness or saturation assumption is needed for these finite overlaps.
This is a local topological prerequisite, not a same-universe analytic
pullback presentation or the localized categorical and etale conclusion
of Task 7349. No external statement is transcribed.
