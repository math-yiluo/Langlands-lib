# The adelic unit-locus obstruction

`AdelicUnitLocusStatement` states the failure of openness discussed in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.4,
first full paragraph beginning “More generally”. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad identifies a basic-open point image with a unit-valued coordinate locus
and states that adelic nonunits can converge to 1, so nonunits need not be closed.

`AffineLineUnitLocusObstruction R S` packages three conclusions for a specified
commutative value algebra with its given topology: its unit subset is not open,
its nonunit subset is not closed, and the image on actual relative `S`-points
of the open immersion from the punctured affine line into the affine line over
`R` is not open. The latter is the range of actual postcomposition by
`affineLinePunctureι R`. The target point space carries the existing
global-section evaluation topology, whose affine-line coordinate equivalence
is a homeomorphism with `S` when `S` is a topological ring.
The general definition only names this proposition; it does not assert these
conclusions for every value algebra.

`NumberFieldUnitLocusStatement` asserts these three conclusions for every
number field, using `R = K` and the original full adelic ring `Adeles K`,
including its archimedean factors. `CurvePlaceUnitLocusStatement` asserts them
for every finite constant field and every specified finite extension of its
rational-function field, using `R = F` and the actual curve-place adelic ring
`CurvePlaceAdeleRing k F`. The rational-function action and compatible scalar
tower are retained; no separability assumption is added. Both clauses use the
existing arithmetic restricted-product topology and diagonal field action.
They do not replace either adelic carrier by an abstract place system.

The combined target is the conjunction of these two clauses, in an arbitrary
common universe. It assumes none of its conclusions and does not require a
supplied sequence or a topology package. The actual point-image description and
the coordinate homeomorphism are already proved in `AffineLinePuncture` and
`AffineLineOrigin`. A separate proof will use adelic nonunits converging to 1.
This statement concerns openness of the image; the separate issue of whether
the point map is a topological embedding is not asserted here.
