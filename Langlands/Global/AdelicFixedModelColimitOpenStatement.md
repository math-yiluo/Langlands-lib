# Open arithmetic stages in actual full-adele model points

`AdelicFixedModelColimitOpenStatement` concerns the actual relative scheme
points of a fixed finite-type model over the original outside-`S` integer
ring, evaluated on the full adele ring. The topology is the existing final
topology `curvePlaceFixedModelAdelePointTopology` or
`numberFieldFixedModelAdelePointTopology`, induced from the original
arithmetic topologies of all finite superlevels containing `S`.

For each superlevel `T`, the map into full-adele points is the actual
`RingPoint.changeRing` map for the literal coefficient inclusion
`curvePlaceAdeleLevelOverι` or `numberFieldAdeleLevelOverι`. It is asserted
to be continuous and open. These conclusions require finite type, expressed
as local finite type and quasi-compactness of the structure map, without
separatedness or affineness.

The second clause gives the precise topology of an image when the stage map
may fail to be injective. `RingPointColimitStageImage` is the actual range
of the stage map into the point colimit. It carries the quotient topology
from that stage, supplied by `ringPointColimitStageImageTopology`. Composing
its inclusion into the colimit with the canonical fixed-model point
comparison is asserted to be an open embedding into actual full-adele
points. Its image is exactly the image of the same stage in the full-adele
point space, since the comparison agrees with coefficient inclusion on
stage representatives. Thus these images carry their quotient topologies
as open subspaces even for nonseparated models.

When the original model is separated, the last clause asserts that each
stage map itself is an open embedding into the full-adele point space.
The scope retains the original scalar actions, arbitrary nonaffine
finite-type models, every finite initial `S` including the empty set, and
an arbitrary common universe. The curve clause retains arbitrary constant
fields with the compatible rational-function algebra and scalar tower in
its stated function-field presentation. The full number-field clause
retains every infinite completion.

This is a derived arithmetic specialization of Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), equation
(3.5.1) and Theorem 3.6 on printed p.6 with transition proof on p.8, and the
opening discussion of topological direct limits in Section 4 on printed
p.9. The finite-type fixed-model comparison supplies the actual point
bijection; continuous open arithmetic transitions and the generic theorem
`filteredRingPointOpenStages` supply the open stage maps and quotient
images. Separatedness supplies injectivity of transitions and hence the
last conclusion. Arbitrary constants and empty initial sets are retained
derived extensions of this argument, not changed source conventions.
This target does not assert independence of the model or initial set,
generic-fiber comparison, local compactness or Hausdorffness.
