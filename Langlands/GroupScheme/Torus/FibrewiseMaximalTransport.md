# Transport of fibrewise maximal tori

This internal module transports the Library predicate
`IsFibrewiseMaximalTorus i` for an actual map `i : T.toGrp ⟶ G`, where
`T` is a commutative group scheme over an arbitrary scheme `S`. The
predicate requires maximality of the actual pullback to the residue field
at every point of `S`; its meaning and source group are unchanged here.
All schemes, field types and coordinate index types lie in the same
arbitrary universe `u`.

The residue-field reflection, arbitrary-base-change and ambient-isomorphism
lemmas are retained from the published module. This extension adds
source-isomorphism transport, its coordinate specialization, and an explicit
proposition with its proof. The provenance is derived from the Library's
residue-field factorization, field-extension reflection, field-point
maximality and actual base-change coherence lemmas; no new geometric
existence input or external structural assertion is assumed.

`isMaximalTorus_residueFibre_of_fieldPoint` applies to a closed inclusion
into any group scheme. It factors a supplied field point through the residue
field of its image, transports maximality to the successive pullbacks using
`isMaximalTorus_baseChange_comp`, and reflects it along the resulting field
extension using `IsMaximalTorus.of_baseChange`. It requires neither
smoothness nor affineness.

`IsFibrewiseMaximalTorus.baseChange` assumes that the ambient group `G`
is smooth and affine over `S`. For every morphism `b : S' ⟶ S`, it proves
fibrewise maximality of the actual pulled-back map from the commutative
base change of `T`. There is no flatness, surjectivity, local-ring or
reductivity assumption on this base change. For each residue point of the
new base, the composite field point has maximal pullback by
`IsFibrewiseMaximalTorus.fieldPoint`; the actual composite-pullback comparison
then gives maximality on the new residue fibre.

`IsFibrewiseMaximalTorus.comp_iso` transports each residue-fibre inclusion
through the pullback of a supplied ambient isomorphism, applying
`IsMaximalTorus.comp_iso` at each residue field. It needs no smoothness or
affineness hypothesis.

`IsFibrewiseMaximalTorus.iso_comp` takes an isomorphism
`e : T'.toGrp ≅ T.toGrp` of the underlying group schemes and transports
fibrewise maximality to `e.hom ≫ i`, with source `T'`. It needs no ambient
smoothness or affineness. The proof pulls `e` back to each residue field
and applies the published field-level `IsMaximalTorus.iso_comp`.
`IsFibrewiseMaximalTorus.iso_comp_iff` gives the resulting equivalence
of predicates; its reverse transport uses the inverse isomorphism.

For any finite coordinate type `I`,
`splitTorus.isFibrewiseMaximalTorus_baseChangedHom` combines arbitrary
base change and source transport. The output map is
`(splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i`,
whose source is the standard coordinate split torus over `S'`.
This applies to an arbitrary base morphism. In particular, when the base
morphism is `algebraBaseMap R K`, this expression is the map called
`splitTorus.baseChangeHom (K := K) G I i` in the existing ring interface;
the target ring need not be a field or a local ring.

`FibrewiseMaximalTransportStatement` is a proposition definition recording
two general properties: arbitrary base-change preservation for a smooth
affine ambient group, and invariance under source isomorphism without
geometric assumptions. It universally quantifies the schemes, groups,
maps and isomorphisms described above. The theorem
`fibrewiseMaximalTransport` proves this conjunction by the two transport
methods. The residue-field reflection and ambient-isomorphism lemmas
remain separate results in the module.

The relative-torus property already has the published transports
`RelativeTorus.IsTorus.baseChange` and `RelativeTorus.IsTorus.of_iso`.
On a member of a relative torus's splitting cover, a chosen isomorphism
from the pulled-back torus to a coordinate split torus permits the
source-isomorphism transport above. The same lemmas then apply to further
local-ring base morphisms. Closedness of a supplied torus map can be
transported separately with `IsClosedSubgroup.baseChange` and `.iso_comp`.

This unit constructs neither a splitting cover nor a quotient group
scheme, and asserts no Weyl-group order or finite étaleness.
