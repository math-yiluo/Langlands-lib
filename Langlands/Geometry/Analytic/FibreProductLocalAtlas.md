# The local affinoid atlas of the unrestricted fibre-product gluing

This internal construction builds an actual indexed affinoid atlas on the
unrestricted fibre-product pair-chart quotient. It assumes domain saturation
of the factor and base atlases, with no global Hausdorff hypothesis. The
field, original space and original index universes are independent. The
constructed space and index universes are `max u w`; this does not yet give
the same-universe object required by the localized etale pullback task.

The selected chart family is `goodChartFamily`: nonempty ranges of original
pairs whose factor charts lie in open Hausdorff patches. These charts embed,
and the full quotient is locally Hausdorff, by `FibreProductLocalCharts`.

The new net proof uses the factor atlas nets. Their preimage-intersection
family is a net on the full quotient. At a point of one such preimage
intersection, choose open Hausdorff factor patches mapping into one open
Hausdorff base patch. In each factor patch, the portion of the specified
original chart has a quasinet of contained original charts: intersect the
ambient original-chart domain with the open-patch domain, then use nested
subspace restriction. Their two preimage refinements combine in the patch
quotient, and the patch chart net refines that preimage family.

The resulting finite relative neighborhood of patch charts transports
through the open subsystem embedding. To verify its neighborhood property
in the full quotient, take an open relative-neighborhood witness in the
patch quotient and map its open part forward. Every selected chart image is
a nonempty good original chart range, contained in the specified factor
preimages and containing the point. Thus the good chart family locally
refines the factor-preimage net and is itself a net.

`LocalAtlasIndex` indexes distinct nonempty actual chart ranges, with one
chosen original good pair representing each range. `localAtlas` retains
that pair's actual affinoid algebra and quotient chart. The range-indexing
gives injectivity of chart domains. Restrictions, chart equations,
universality and identity/composition laws are the existing actual
`rangeRestriction` construction. The embedded-chart, local-Hausdorff and
net results discharge the remaining atlas axioms. `localPresentation`
packages this atlas with the actual quotient topological space.

No same-universe shrinking, complete strong projection construction,
localized universal property or etale base change is asserted here. No
external statement is transcribed.
