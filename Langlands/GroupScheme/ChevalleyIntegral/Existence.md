# A single integral reductive realization with a common full field-fibre root datum

The final theorem has exactly the type
`Langlands.GroupScheme.ChevalleyIntegralExistenceStatement.{u}`.
Its composition uses `integralExistence_of_smoothClosure` and the
smoothness of the fixed integer Chevalley closures. The following explains
the route through those supporting results.

The coordinate normalization chooses a finite coordinate type and a root
datum on both entire coordinate lattices, with their standard perfect
pairing, together with a full root-pairing equivalence from the original
datum. It retains all central lattice directions and permits empty root
systems. The existing field construction supplies the generic Chevalley
group for a full coordinate Chevalley datum. Its schematic closure in the
integral general linear group gives an affine flat integral model.

The full ordered negative-root, torus and positive-root parameter scheme
is an open subscheme of this closure. Its field base changes are smooth
and nonempty. Smoothness of a locally finite-type group over a field follows
from a nonempty smooth open chart by translation after extension to an
algebraic closure and descent. The fibrewise smoothness criterion then
gives smoothness of the integral closure.

Choose the relative identity-component family of this smooth closure.
The generic group is geometrically connected and integral. The Dedekind
neutral-model construction gives an actual affine smooth integral model
with geometrically connected fibres. The full integral coordinate torus
factors through this family and remains a closed subgroup. These choices
precede the field quantifiers.

In every supplied field fibre, the full ordered cell gives a nonempty open
of the full closure fibre. An explicit parameter point has zero root
coordinates and the identity torus coordinate. On all test schemes, the
base-changed ordered product factors through each supplied field Chevalley
embedding, so that open is contained in its image. Pulling the open back
to the neutral fibre, geometric integrality and closedness make the
neutral field embedding surjective. Since the neutral fibre is reduced,
the closed immersion is an actual isomorphism. The full torus comparison
commutes with that isomorphism.

These actual compatible field isomorphisms prove reductivity of the one
integral family and maximality of its fixed coordinate torus on every
field fibre. They transport the full common coordinate root datum,
including the roots, coroots, entire pairing and normalizer reflections,
through `IsFibrewiseRootDatumOf`. Coordinate normalization then gives the
unchanged target for the original root datum in every universe.

This proof uses the neutral family and requires no connectedness assertion
for the full schematic closure. It proves the stated fibrewise
root-datum realization; it does not add the relative root-space or pinning
claims of the stronger relative split-group classification.
