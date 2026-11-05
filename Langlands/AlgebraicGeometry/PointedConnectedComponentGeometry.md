# Geometric connectedness of connected schemes with rational points

This internal supporting unit proves geometric connectedness of an arbitrary
connected scheme over a field when the structure morphism has an actual
rational section. It requires no finite type, smoothness, reducedness,
quasi-compactness or separation assumption for this theorem.

Over an algebraically closed field, the actual projection after a field
extension is an open surjective map. The published FLT helper
`IsAlgClosed.BaseChangeIrreducible.irreducibleSpace_fiber_fst` proves that
every actual residue fibre of this projection is irreducible, with no
condition on the original source scheme. Its image is therefore connected.
Mathlib's connected-preimage theorem for a quotient map with connected
fibres shows that a connected source scheme stays connected after every
field extension. This proves
`geometricallyConnected_of_connected_isAlgClosed`.

For a general field, extend to its algebraic closure. The projection is
open, since it is a base change of a field-spectrum morphism, and closed,
since the algebraic closure is integral. Its fibre over the rational point
is a singleton: pulling the projection back along the section gives
the spectrum of the algebraic closure, by the published `sectionFiberIso`.
An open and closed map to a connected space with a nonempty singleton fibre
has connected source. The proof uses a clopen partition: the images of both
nonempty parts would be the whole base and would split the singleton fibre.
The algebraic-closure base change is consequently connected. The
algebraically closed field result makes it geometrically connected, and
the published surjective-base-change descent theorem returns geometric
connectedness over the original field.

The singleton-fibre argument reuses
`connectedSpace_of_open_closed_singleton_fiber` from Worker 513's published
`SmoothPointedGeometricConnectedness` unit. Here smoothness is replaced by
the preceding general algebraically closed field result, so no integrality
or domain-stalk conclusion about the scheme is needed.

For a locally Noetherian scheme, `connectedComponentOpen` equips its actual
connected component with the open-subscheme structure using the published
openness theorem. It is connected. A rational section factors through
this component because its domain has only one point.
`connectedComponentSection` is this actual factorization through the open
immersion; composing it with the restricted structure morphism is the
identity. Applying the general pointed theorem proves geometric
connectedness of the component.

For a locally finite type morphism of arbitrary schemes, the actual
residue fibres are locally Noetherian. `SectionComponent.fiberComponentOpen`
is the open connected component through the previously defined actual
`fiberPoint`. Its structure morphism to the residue-field spectrum is
geometrically connected, by the actual `fiberSection` and its section
identity. This is the fibre-component input used in EGA IV, Troisième
partie (1966), Corollary 15.6.5, printed pp.238–239 / retained PDF
pages237–238, registered source `ega-iv3-grothendieck-dieudonne-1966`,
SHA-256 `f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`.
The route is internal and uses the named Library and Mathlib results.
It does not prove openness of the union over the base.
