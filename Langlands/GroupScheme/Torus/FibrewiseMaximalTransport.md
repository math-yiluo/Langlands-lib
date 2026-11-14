# Fibrewise maximality under base change and source isomorphisms

This internal helper transports the Library predicate
`IsFibrewiseMaximalTorus i` for an actual map `i : T.toGrp ⟶ G`, with
`T` a commutative group scheme over an arbitrary scheme `S`. The predicate
requires maximality of the actual pullback to the residue field at every
point of `S`; its meaning and source group are unchanged here.
All schemes, field types and coordinate index types lie in the same
arbitrary universe `u`.

`FibrewiseMaximalTransportStatement` is a proposition definition recording
two general properties: arbitrary base-change preservation for a smooth
affine ambient group, and invariance under source isomorphism without
geometric assumptions. It universally quantifies the schemes, groups,
maps and isomorphisms described below. The theorem
`fibrewiseMaximalTransport` proves this conjunction by the two transport
methods in this module. The coordinate split-torus result is a further
specialization of these same methods.

`IsFibrewiseMaximalTorus.baseChange` assumes that the ambient group `G`
is smooth and affine over `S`. For every morphism `b : S' ⟶ S`, it proves
fibrewise maximality of the actual pulled-back map from the commutative
base change of `T`. There is no flatness, surjectivity, local-ring or
reductivity assumption on this base change.

For a point `s` of `S'`, the composite of its residue-field map with `b`
is a supplied field-valued point of `S`. The published
`IsFibrewiseMaximalTorus.fieldPoint` gives maximality on that composite
fibre, using smoothness and affineness of the original ambient group.
The published `isMaximalTorus_baseChange_comp` then identifies this
maximality with maximality in the successive pullbacks, which is exactly
the residue fibre of the pulled-back map.

`IsFibrewiseMaximalTorus.iso_comp` takes an isomorphism
`e : T'.toGrp ≅ T.toGrp` of the underlying group schemes and transports
fibrewise maximality to `e.hom ≫ i`, with source `T'`. It needs no ambient
smoothness or affineness. The proof pulls `e` back to each residue field
and applies the published field-level `IsMaximalTorus.iso_comp`.
`IsFibrewiseMaximalTorus.iso_comp_iff` gives the resulting equivalence
of predicates; its reverse transport uses the inverse isomorphism.

For any finite coordinate type `I`,
`splitTorus.isFibrewiseMaximalTorus_baseChangedHom` combines these two
transports. The output map is
`(splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i`,
whose source is the standard coordinate split torus over `S'`.
This applies to an arbitrary base morphism. In particular, when the base
morphism is `algebraBaseMap R K`, this expression is the map called
`splitTorus.baseChangeHom (K := K) G I i` in the existing ring interface;
the target ring need not be a field or a local ring.

The relative-torus property already has the published transports
`RelativeTorus.IsTorus.baseChange` and `RelativeTorus.IsTorus.of_iso`;
this helper does not redefine them. On a member of a relative torus's
splitting cover, a chosen isomorphism from the pulled-back torus to a
coordinate split torus permits the source-isomorphism transport above.
The same lemmas then apply to further local-ring base morphisms.
Closedness of a supplied torus map can be transported separately with
the existing `IsClosedSubgroup.baseChange` and `.iso_comp`.

The provenance is derived: every result composes the imported Library's
field-point maximality and actual composite-pullback and source-isomorphism
transports. No new external structural assertion is assumed. This unit
constructs neither a splitting cover nor a quotient group scheme, and
asserts no Weyl-group order or finite étaleness.

## Retained residue and ambient transport

# Transport of fibrewise maximal tori

This module provides internal transport lemmas for the actual inclusions used
in the proof of étale-local maximal-torus existence. Its provenance is the
published residue-field factorization, field-extension reflection of maximality,
and base-change coherence lemmas in the Library; it introduces no new
geometric existence input.

`isMaximalTorus_residueFibre_of_fieldPoint` applies to a closed inclusion into
any group scheme. It factors a supplied field point through the residue field
of its image, transports maximality to the successive pullbacks, and reflects
it along the resulting field extension using `IsMaximalTorus.of_baseChange`.
It requires neither smoothness nor affineness.

`IsFibrewiseMaximalTorus.baseChange` requires the ambient group to be smooth
and affine. For each residue point of the new base, the composite field point
has maximal pullback by `IsFibrewiseMaximalTorus.fieldPoint`; the base-change
comparison then gives the required maximality on the new residue fibre.

`IsFibrewiseMaximalTorus.comp_iso` transports each residue-fibre inclusion
through the pullback of the supplied ambient isomorphism. It needs no
smoothness or affineness hypothesis.
