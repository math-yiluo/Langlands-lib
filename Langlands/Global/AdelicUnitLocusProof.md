# Proof of the adelic unit-locus obstruction

This module proves `Langlands.Global.AdelicUnitLocusStatement` from the paired
statement module. Its source assertion is Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (2011), printed p.4, first full paragraph
beginning “More generally”. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The explicit sequence is the derived construction in `AdelicNonunitSequence`.

The general helper starts with a sequence of nonunits converging to 1 in a
commutative topological value algebra. If the nonunit locus were closed, the
closed-set limit theorem would make 1 a nonunit, contradicting its
invertibility. Openness of the unit locus would make the complementary nonunit
locus closed, so it also fails.

For the assertion on actual scheme points, the existing
`range_affineLinePuncture_points` identifies the point image of the actual
punctured-affine-line open immersion with the unit-coordinate locus.
Pulling back an open image along the inverse of `affineLinePointHomeomorph`
would make the unit locus open in the original value-ring topology. This
contradicts the preceding conclusion. No topology on the source point space
or embedding assertion is needed for this image-openness argument.

`numberFieldUnitLocus` applies the helper to `numberFieldNonunitSequence`,
whose archimedean coordinates all equal 1 and whose finite part has a zero
at one new actual place at each step. `curvePlaceUnitLocus` uses the analogous
sequence at actual curve places. Their already proved convergence holds in
the original restricted-product topologies. The function-field specialization
uses the existing diagonal field algebra action over finite constants and
adds no separability assumption. `adelicUnitLocus` combines these proofs
without changing any hypothesis or the arbitrary common universe of the target.
