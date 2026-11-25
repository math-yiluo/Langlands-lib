# Detecting isomorphisms on the two fibres of a discrete valuation ring

This internal module defines `IsGenericSpecialFibreIsomorphism` for a specified
morphism of schemes over a local ring with a chosen field algebra. It means
that the pullback of the morphism to that field and its pullback to the canonical
residue field are both isomorphisms. The predicate alone imposes no
fraction-field hypothesis; the DVR lemmas explicitly require that the chosen
field is a fraction field.

`isIso_of_residueField_fibres` concerns an arbitrary base scheme. Its source
structure map is flat and locally of finite presentation, and its target
structure map is locally of finite type. It proves that the actual morphism is
an isomorphism if every residue-field fibre is. The published criterion
`isOpenImmersion_of_fiberwise` makes it an open immersion, and the published
fibrewise surjectivity criterion makes it surjective.

`isIso_field_pullback_of_generic_special` assumes a domain DVR and a chosen
fraction field. A ring homomorphism from the DVR to a field is either injective,
in which case it extends to the fraction field, or its prime kernel is the
maximal ideal, in which case it factors through the canonical residue field.
In each case the given field-valued pullback is a further base change of an
isomorphism.

`isIso_of_generic_special` applies this factorization to the residue field of
every point of `Spec R`, then applies the preceding arbitrary-base criterion.
It needs a flat, locally finitely presented source and a locally finite-type
target. It imposes no Henselian or reductivity hypothesis.

The provenance is internal composition of the imported Library fibrewise
open-immersion and surjectivity criteria with Mathlib's fraction-field
universal property, prime ideals in a DVR, residue-field factorization and
pullback comparison. This supplies the passage from generic and closed fibre
isomorphisms to an integral isomorphism; it supplies neither such fibre
isomorphisms for a reductive-group homomorphism nor the arbitrary-base
fibrewise-isogeny theorem.
