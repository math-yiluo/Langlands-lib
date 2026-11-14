# Full dynamic factors of local-isogeny graphs

This internal derived module constructs smooth closed representatives of both
entire intrinsic unipotent factors of an actual source-simple isogeny graph.
The actual source graph torus represents the whole middle dynamic centralizer,
is self-centralizing, and is maximal after every field extension in the same
universe.

The data are a `SimpleIsogenyGraph D` for actual torus inclusions
`i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G'` and a torus map `t : T ⟶ T'`
over a field `k`. Both ambient groups are smooth and affine. The graph record
retains the source split torus, its generic chamber and simple-root directions,
the actual local isogenies and their generated closed graph envelope.

`SimpleIsogenyGraph.GraphDynamicFactors D` records the smooth closed rational
closure envelopes of `D.negativeGenerated` and `D.positiveGenerated`. Their
inclusions represent the full dynamic unipotent subgroup functors for the
opposite chamber and the chamber in the graph. Its `torusRep` field says that
`D.envelope.torusLift`, whose source is the original `T`, represents the full
chamber centralizer. All three assertions hold on every scheme test. They do
not identify the abstract generated rational subgroups with all rational points
of their closures.

`graphDynamicFactors` constructs this record over an algebraically closed
field. It assumes connectedness of `G`, closedness of `i`, the all-test identity
that the source chamber centralizer is `range i`, and finite reduced realizing
root data `P`, `P'` on the actual character and cocharacter lattices. Both
lattice pairs are finite over the integers; `T'` is split. The supplied
`RootDatumIsogeny p P' P` and actual character equation
`t ≫ χ = f.weightMap χ` retain all root factors. At this step the natural
parameter `p` need not be identified with the field's characteristic exponent.

The construction chooses the two actual rational closure envelopes. Containment
of their generating rational points in the intrinsic closed dynamic factors
implies containment of the whole envelopes, using
`RationalClosureEnvelope.range_le_of_rationalPoints_le`. The source graph torus
lies in the chamber centralizer. Each generating rational point factors through
its closure inclusion, so the previously proved dense rational graph cell is
contained in the literal rational triple product of these three closed
inclusions.

The imported generic theorem
`isRepresentedBy_dynamicFactors_of_dense_closed_subcell` now fills all three
factors. It compares these closed subgroups with the smooth intrinsic dynamic
factors inside their open triple cell. Density gives dominance of the product
of the coordinate comparisons. A closed condition containing this dominant
image holds on the whole product; a coordinate section and reducedness give
actual factorization of each entire larger factor through the smaller one.
Thus this argument gives equal subgroup functors on every test, rather than
only equality of underlying point sets.

The primary constructor `graphDynamicFactorsOfReductive` replaces the explicit
source connectedness, closedness and chamber-centralizer identity by
`IsConnectedReductive G` and `IsMaximalTorus i`. It derives connectedness from
reductivity and the centralizer identity from the source generic chamber and
maximality. The algebraic closedness, root-data, split target torus, isogeny and
character-map hypotheses remain.

For a supplied `GraphDynamicFactors E`, the module registers smoothness,
affineness and connectedness of the two closure groups. Connectedness follows
from their representations of intrinsic dynamic unipotent factors.
`torus_selfCentralizing` proves that the whole-torus centralizer of the source
graph torus equals its range: it lies in the chamber centralizer represented by
that torus, and the reverse inclusion follows from commutativity.
`isMaximalTorus` uses source closedness and the existing self-centralizing-torus
criterion. `isMaximalTorus_baseChange` applies its field-extension version to
every field extension in universe `u`. These consequences require no additional
algebraic closedness assumption beyond the supplied certificate.

The provenance is the existing common-torus graph dynamic-factor construction,
adapted to distinct tori and local isogenies by the proved isogeny graph-cell
density. The generic closed-subcell theorem and self-centralizing-torus criteria
are reused directly; no additional literature result is asserted. Target
coverage, graph reductivity, invertibility of the factor restrictions and first
projection, the second projection's isogeny property, and the general
realization and fixed-torus extension theorem remain separate obligations.
