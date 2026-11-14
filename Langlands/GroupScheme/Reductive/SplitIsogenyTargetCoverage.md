# Target simple-root coverage for local-isogeny graphs

This derived support module works over arbitrary fields and with the actual
character and cocharacter lattices. A root-datum isogeny goes from the target
datum to the source datum, so its coweight map pushes a source chamber to the
target torus. The transpose relation and the root equations show that every
target root pairing is the corresponding source pairing times its positive
characteristic-power root factor. Consequently signs and genericity pass to
the pushed chamber without any base-transport assumption.

The subsequent simple-system comparison takes
`RootDatumIsogenyBaseStatement` as an explicit input. It constructs an integral
base adapted to the generic source chamber, transports this base, and compares
base positivity to the intrinsic positive roots. Positive indecomposable roots
are exactly the simple supports. This identifies the target simple roots with
the source simple roots through the given root bijection.

For a `SimpleIsogenyGraph` whose actual torus map has the prescribed character
pullback, every target simple root therefore corresponds to one source simple
index. That source direction annihilates its simple root. The actual
cocharacter map and the graph's direction-composition equation transfer this
annihilation to the target direction. Thus the target directions cover the
simple roots of the pushed generic chamber.

`SimpleIsogenyGraph.second_geometry_of_base_transport` applies this coverage
and the generic-chamber centralizer theorem to the graph's second projection.
Its hypotheses require the ambient target to be connected reductive, its
specified torus to be split maximal, and the actual torus map to be an isogeny.
The result records flatness, surjectivity, local finite presentation and
quasi-compactness of the projection.

`SimpleIsogenyGraph.faithfullyFlatGraph_of_base_transport` combines this
geometry with the source projection geometry already supplied by the
source-simple graph. Finally,
`SimpleIsogenyGraph.reductiveGraph_of_base_transport` applies the graph
reductivity theorem: after algebraic closure a normal unipotent subgroup maps
trivially into both connected reductive ambient groups, and the closed graph
in their product has jointly injective projections on every scheme test.
The resulting certificate retains the original graph and both projection
geometries. These constructors still take base transport as an explicit
proposition argument; they do not supply its proof.

The provenance is the published integral coweight-base construction, the
published positive-indecomposable characterization of simple roots, and the
local-isogeny graph's actual maps and projection/reductivity criteria. This
module does not prove the assumed base-transport proposition or the ambient
split isogeny theorem. It retains all positive characteristic-power factors
and imposes no smooth-kernel hypothesis.
