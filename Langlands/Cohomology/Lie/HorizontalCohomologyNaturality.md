# Commutative squares on actual horizontal cohomology

This internal construction uses `HorizontalCohomologyIntertwiner` on four genuine coefficient modules with the same Lie algebra, horizontal submodule, compact covariance action, and finite translation monoid. Each coefficient module retains its own Lie action, compact representation, proved insertion identity, horizontal differential, and differential-compatible finite action. The four maps are actual equivariant chain maps.

`IntertwinerSquare` bundles four equivariant edge maps between four original representations with the equality `right.comp top = bottom.comp left`. It retains the maps as data, allowing consumers to access every transported edge together with the commutation law.

`mapCyclesIntertwinerSquare` constructs this bundled square on the existing differential kernels in each degree. Its four fields are the existing cycle transports of the supplied top, right, left and bottom cochain maps. Its commutation field is `mapCyclesIntertwiner_square`, which uses intertwiner extensionality, cycle subtype extensionality, and the given cochain equality evaluated at a closed cochain.

`mapCohomologyIntertwinerSquare` constructs the corresponding bundled square on the existing quotients of cycles by differential-image boundaries. Its four fields are the existing quotient transports of the same four maps. Its commutation field is `mapCohomologyIntertwiner_square`. Surjectivity of the original quotient projection reduces this equality to a cycle representative; the existing representative formulas reduce it to the original cochain square.

These constructors introduce no new coefficient objects or identifications. Their assumptions are precisely the original covariance, insertion, differential-compatible finite actions, four equivariant chain maps and their commuting square. All four coefficient universes, the scalar field, Lie algebra, compact group and translation monoid are independent. This is an internal consequence of the previously implemented kernel and quotient constructions, with no new original-source claim.
