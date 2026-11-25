# Base change of supplied universal maximal-torus families

This internal helper derives base-change stability directly from the
Library's `IsUniversalMaximal` all-test universal property. It reuses
`pullFamily`, `pushFamily`, `baseParameter`, and the comparison of their
actual evaluated subgroup ranges from `HomScheme/ChartCoverBaseChange`.
No maximal-torus existence theorem or geometric property of the parameter
scheme is assumed or proved here.

`evaluate_pullFamily_range_iff` says that evaluation after changing the
base equals a supplied subgroup precisely when the original evaluation
at the adjoint parameter equals the supplied subgroup transported to
the original ambient pullback. The proof reflects equality of ranges
through the canonical ambient isomorphism.

`pullMaximalClassifier` constructs the classifier on the new base by
choosing the original universal classifier of the transported subgroup
and applying the map/pullback adjunction. Its evaluation theorem proves
that this morphism classifies the supplied subgroup.

`IsUniversalMaximal.pullFamily` holds for any ambient group and any base
change. A closed fibrewise maximal relative torus over a test scheme
on the new base is transported through that isomorphism and classified
by the original universal property. The map/pullback adjunction on
slice categories transfers existence and uniqueness of the classifier
to the changed parameter scheme.

`isFibrewiseMaximalTorus_pullFamily` assumes that the original ambient
group is smooth and affine. The proof preserves fibrewise maximality
under evaluation at the parameter projection and then through the
inverse ambient comparison. Relative torus structure and closedness
of the pulled family are already supplied by the existing Library
base-change results.
