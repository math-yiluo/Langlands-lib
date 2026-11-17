# Underlying point lifting for localized pullbacks

This internal result is derived from the published analytic fibre-product
construction. It is intended as a reusable input to the algebraic-space
analytification immersion proof and the separatedness proof. `HasPointLifting p q f g` means that every pair of points of the two
upper-right and lower-left objects with equal images in the lower-right
object has a preimage in the upper-left object with the prescribed
projections. It does not include a commutativity assertion. The theorem
`hasPointLifting_of_isPullback` proves this condition for every categorical
pullback. Neither uniqueness nor preservation of topological pullbacks
is asserted.

For a complete ultrametric normed field `K : Type u`, all saturated
presentations and localized objects here have field, ambient-space and
chart-index universes `u, u, u`. Thus the smallness requirements of the
actual small fibre-product cone hold automatically. No Hausdorff, étale,
nontrivial-norm or local-finiteness hypothesis is used.

`exists_smallFibreProduct_point` applies the published
`FibreProduct.exists_point` to two strong arrows and compatible points.
The canonical shrinking homeomorphism transports the resulting point to
`smallFibreProduct`; its projection formulas give the required images.
`exists_point_of_isPullback_strong` applies a given categorical pullback's
universal property to that cone and evaluates the projection equations.

`exists_point_of_isPullback` handles arbitrary localized objects and
arrows. Each object is an original presentation in the constructed
localization. Right fractions supply strong numerators and full
quasi-isomorphism denominators. The inverse denominator homeomorphisms
lift the original pair of points to compatible points for the strong
numerators. Their small fibre-product cone maps to the given localized
pullback after composing its projections with the denominators. Evaluating
the universal map at the constructed point proves the two equations.

The provenance is the above internal argument using the published `FibreProductPoints`,
`FibreProductLocalizedLimit`, `SaturatedLocalizedFractions` and
`SaturatedStrongLocalization` interfaces. It does not prove the full
`SpaceAnalytificationImmersionStatement`.
