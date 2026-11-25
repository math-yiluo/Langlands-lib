# Coordinate tori in the split affine rigidity reduction

This internal derived module unpacks the supplied coordinate packages in
`SplitAffineIsogenyTorusConjugacyStatement`. It does not prove the local
existence proposition.

`fppfLocallyTorusConjugate_torusIso_iff` identifies fppf local conjugacy
for an inclusion and for that inclusion precomposed with an isomorphism
of commutative group schemes. The cover is unchanged. In the forward
direction each conjugating point is composed with the isomorphism; in
the reverse direction it is composed with the inverse. The imported
all-test predicate equivalence and the isomorphism identities give the
required conjugation equations. No torus, isogeny, reductivity or
affineness hypothesis is needed for this transport.

`CoordinateSplitIsogenyTorusConjugacyStatement` states local existence
over every affine base using actual coordinate split tori. Both groups
are reductive. Each coordinate inclusion is closed and fibrewise
maximal, has a full coordinate root datum on every field-valued fibre,
and has free actual root-weight lines. Two isogenies have the same
restriction to the source coordinate torus, and the first restriction
factors through the target coordinate torus. The conclusion is fppf
local all-test conjugacy in that target torus. The fibrewise root-datum
predicates include finiteness and reducedness of each root datum. No
compatibility of the isogenies with these two root data is assumed.

`splitAffineIsogenyTorusConjugacy_of_coordinateSplit` derives the
packaged split affine assertion from this coordinate assertion. Unpack
the two coordinate packages. The new coordinate-torus map is the
source coordinate isomorphism, followed by the original torus map,
followed by the inverse target coordinate isomorphism. Its torus square
follows by cancellation. Equality of restrictions is precomposed with
the source coordinate isomorphism. Apply the coordinate assertion and
transport its local conjugators through the target coordinate
isomorphism.

`coordinateSplitIsogenyTorusConjugacy_of_splitAffine` proves the reverse
implication by packaging the supplied data with identity coordinate
isomorphisms. Thus
`splitAffineIsogenyTorusConjugacy_iff_coordinateSplit` is an equivalence
of the two local existence propositions. The final theorem
`reductiveIsogenyTorusRigidity_of_coordinateSplit` composes the forward
reduction with the imported general-base reduction, obtaining the
unchanged global rigidity statement from coordinate local existence.

The provenance is the imported definitions of full split coordinate
packages, all-test conjugation transport, and the general-base
reduction. These are formal unpacking and transport arguments, with no
new external source. Local existence, including intrinsic root-datum
compatibility of the isogenies, is not proved in this module.
All results preserve the universe and permit nonreduced and empty
bases.
