# Reduction of polarized representability descent to scheme effectivity

Assume `PolarizedEtaleRelationEffectivityStatement` in scheme universe `u`.
Then the unchanged `PolarizedSmoothProperEtaleDescentStatement` holds for
every independently chosen presheaf-value universe `v`.

`LocalRepresenter.descendedRepresenter` constructs a global representing
object and its `RepresentableBy` datum from this effectivity hypothesis and
the original local polarized smooth proper representation. It first uses
`LocalRepresenter.etaleRelation` for the actual relation on the local
representing scheme. `LocalRepresenter.cartesian` identifies this relation
with the overlap over the covering base. The actual coherent polarization is
`LocalRepresenter.equivariantBundle`; its bundle is definitionally the
given local universal line bundle, so the original ampleness premise
applies directly.

Geometric effectivity supplies a scheme over the original base and an
invariant chart map with the prescribed cartesian square. Classical choice
selects that scheme and chart map. `LocalRepresenter.representableByDescent`
then constructs the representation of the original big étale sheaf by
comparing the two locally surjective sheaf presentations and their kernels.
Its temporary universe lift and subsequent lowering preserve the original
independent value universe.

The accompanying theorem
`polarizedSmoothProperEtaleDescent_of_effectivity` applies this constructor.
`geometricReflection_of_representable` then reflects smoothness, properness
and ampleness of the same coherent universal line bundle from the local
representer. Étaleness supplies the flatness needed for that reflection.
Thus its conclusion is precisely the published target proposition, under
the explicit geometric effectivity hypothesis.

The provenance is internal composition of the local relation, coherent
bundle, sheaf comparison and geometric reflection constructions. This module
does not prove geometric effectivity, and therefore does not by itself
prove the unconditional target. Neither the target nor its imported
definitions is changed.
