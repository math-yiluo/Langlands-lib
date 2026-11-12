# Connected fibres tested on a surjective étale target atlas

This internal supporting module proves that nonempty geometrically connected
fibres can be tested after pulling an algebraic-space morphism back along a
surjective étale target scheme chart. The pullback is the actual
`fibreProduct`, and its projection is `FibreProduct.snd`. No finiteness,
quasi-separatedness or representability condition is imposed on the
algebraic-space morphism. Both directions use exactly the published
`HasGeometricallyConnectedFibres` predicate, including nonemptiness.

`exists_lift_atlas_algClosed` first establishes lifting of sections through
a surjective étale scheme chart of an arbitrary presheaf. Pull the chart
back over a section on `Spec K`, with `K` algebraically closed. Its actual
represented projection to `Spec K` is étale and surjective. Choose a point
by surjectivity, then a closed specialization, using local finite type
over the field. Mathlib's `pointOfClosedPoint` gives a `K`-point at this
closed point whose composite with the projection is the identity. Equip
this section with its original structure map over `S`. Composing with the
other projection gives a morphism `Spec K → V` over `S`, and the cartesian
square shows that its image under the chart is exactly the supplied
section. The target presheaf need not be a sheaf.

`iteratedFibrePullbackIso` constructs the full-presheaf isomorphism for a
second fibre of any cartesian square. Pasting the defining square of this
second fibre with the supplied cartesian square gives a cartesian square
for the direct fibre. Its canonical `isoPullback` is the desired
isomorphism. It retains the actual presheaf fibres and imposes no
representability condition on them.

For the forward implication of
`hasGeometricallyConnectedFibres_iff_targetAtlas`, a field test of the
pullback projection gives the composite field test of the original
morphism. The preceding isomorphism induces a homeomorphism of point
spaces and transfers the original connectedness to the pullback fibre.

For the converse, the algebraically closed field-test criterion from
`GeometricFibreFieldTests` reduces the assertion to algebraically closed
fields. Lift each target section through the chosen target atlas by the
first lemma. The connectedness hypothesis applies to that lifted test of
the actual pullback projection. The iterated-fibre isomorphism, followed
by the pullback isomorphism for the equality of the lifted composite with
the original section, identifies its point space with the requested
original fibre. The induced homeomorphism transfers connectedness and
nonemptiness to that fibre.

The provenance is internal: this combines actual represented chart
pullbacks, field-scheme closed points, Mathlib's algebraically closed
point construction, pullback pasting and point-topology isomorphisms.
No external assertion or eventual-descent premise is assumed. It is a
target-atlas criterion for the remaining connected-fibre clause, not a
proof of eventual limit descent or of the full
`SpaceLimitPropertyDescentStatement`.
