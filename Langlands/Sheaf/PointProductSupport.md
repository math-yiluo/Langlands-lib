# Coordinates and support of actual point products

This internal extension of `PointProduct` makes its module section formula
concrete and proves support control and lifting for its actual sections.
It uses the actual product projections and Mathlib's module product
isomorphism. `sectionCoordinates` parametrizes sections over `X` by a
coefficient for each point and each element of its fiber over `X`.
For a terminal object, `globalCoordinates` removes the singleton fiber
indices, giving arbitrary coefficients indexed by the site points.
The index universe is `wI`; the point fibers and coefficient modules lie in
universe `max wI w`. Thus the indices may lie in a smaller universe than the
fibers. The site object and morphism universes remain independent.

`sectionCoordinate_restrict` identifies restriction with pullback of the fiber
index. `coefficientRetraction` is the diagonal adjunction map from the actual
fiber of the product to its coefficient. `germ_coefficientRetraction` proves
that applying it to a germ recovers the corresponding section coordinate.
Consequently a nonzero coordinate gives a nonzero germ.
`coefficientSupport_subset_support` gives this inclusion over a terminal
object as an inclusion of the nonzero coefficient set in the actual germ
support defined in `PointSupport`.

The opposite bound needs site neighborhoods. `SeparatesComplement points X K`
means that every fiber element at an index outside `K` lifts to some
neighborhood over `X` on which every nonempty point fiber has its index outside
`K`. `support_subset_of_sectionCoordinates_zero` then bounds the actual germ
support by `K` if every coordinate outside `K` vanishes. Its proof restricts
to the supplied neighborhood, proves that restriction zero using the concrete
coordinates, and applies the restriction identity for germs.

`exists_lift_with_support` proves that, over a terminal object, a
coefficientwise surjective family map lifts every section with support in
such a `K` to a section with support in the same `K`. The proof chooses a
preimage coefficient at each nonzero coefficient and chooses zero at the
zero coefficients. The original section's germ support contains its nonzero
coefficient set, so the new coefficients vanish outside `K`, and the support
bound just proved applies.

`HasCompactSeparatingBounds` asks that every compact subset of the point
index space have a compact enlargement satisfying `SeparatesComplement`.
`compactSections_map_surjective` applies the lifting result to such an
enlargement. It proves surjectivity of the actual `sheafCompactSections`
map on the corresponding products, with no replacement support convention.

All statements are internal consequences of the product and site fiber APIs.
The neighborhood and compact-bound conditions are explicit hypotheses; this
module does not assert that an arbitrary site or an analytic site satisfies
them. Analytic specialization and derived-functor vanishing are further
obligations.
