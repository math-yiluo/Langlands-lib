# Root-function families under actual cross-torus transport

Author: Worker 118.

For an arbitrary field, supply actual commutative-group isomorphism `e : S ≅ S'`
and ambient group-scheme isomorphism `f : G ≅ H`. The constructor
`RootFunctionFamily.transportEquiv e f` reindexes a full root-function family:
its value at the target character `a'` and target point `g'` is the original
value at `(characterLattice.congr e).symm a'` and `rationalPoints.map f.inv g'`.
Its inverse uses the forward maps. Both inverse laws follow from the actual
isomorphism laws. In particular the value on simultaneous forward images is
unchanged, including characters off the roots and points off the root groups.

The equivalence intertwines the original real-cocharacter translations along
`cocharacterRealCongr e`. This follows from invariance of evaluation under
simultaneous actual character and cocharacter transport. Surjectivity of the
real map and injectivity of the family equivalence give preservation and
reflection of equipollence.

For morphisms `i : S.toGrp → G` and `j : S'.toGrp → H` with the actual square
`i ≫ f.hom = groupHom e.hom ≫ j`, the existing all-test root-group transport
specializes to preservation and reflection of rational root-group membership.
The unchanged-value formula then gives preservation and reflection of every
filtration set at the same real level. If both inclusions are monomorphisms,
the family equivalence also intertwines the original normalizer actions,
using exactly `normalizerPointsTransportEquiv e f h`. The proof reindexes both
arguments by surjectivity, then uses the published character-action identity
and the actual ambient homomorphism's multiplication and inversion laws.

This unit has internal provenance: it reindexes existing full function
families along supplied actual isomorphisms and establishes intrinsic
identities from the published character, root-group, normalizer and pairing
transport. No external mathematical existence assertion is introduced.
The unit does not yet transport the valuation axioms, split-torus compatibility,
valid apartment data, apartment points, full building data or the A2 axiom.
