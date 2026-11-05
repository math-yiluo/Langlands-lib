# Field criteria for geometric irreducibility

This internal unit supplies geometric irreducibility comparisons for actual
schemes in arbitrary common universe `u`. It is derived from the published
algebraically closed field theorem and Mathlib's pullback, radicial morphism,
integral morphism and purely inseparable extension APIs. It imposes no finite
type, quasi-compactness, separation, reducedness or characteristic hypothesis.

`geometricallyIrreducible_of_surjective_baseChange` descends geometric
irreducibility through any surjective morphism of bases. For a field-valued
test of the original morphism, surjectivity supplies a point after pulling
back the base cover. Its residue field gives a common further field test.
The assumed geometric irreducibility makes this further pullback irreducible;
its continuous surjective map to the original test descends irreducibility.
The pullback-pasting route is the same general descent argument as the
published `GeometricallyConnected` descent proof, with irreducibility of the
continuous image in place of connectedness.

`universallyInjective_specMap_of_isPurelyInseparable` applies the
field-valued-points characterization of universally injective morphisms.
Restriction of ring homomorphisms through a purely inseparable field
extension is injective into any field. Thus the corresponding spectrum map
is universally injective.

The construction `purelyInseparableBaseChangeHomeomorph` combines that injectivity
with integrality and surjectivity of a purely inseparable field spectrum map.
Its scalar-extension projection is a continuous closed bijection, hence a
homeomorphism. Its forward map is the actual first projection. The theorem
`irreducibleSpace_pullback_of_isPurelyInseparable` transfers irreducibility
through that homeomorphism.

Finally, `geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed`
extends a separably closed field to its algebraic closure. This extension
is purely inseparable, so the scalar extension remains irreducible. The
published theorem
`AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed`
makes it geometrically irreducible over the closure. Surjective descent
then proves geometric irreducibility over the original separably closed field.

These results provide field criteria only. They do not construct a finite
separable extension or descend irreducible components to such an extension.
