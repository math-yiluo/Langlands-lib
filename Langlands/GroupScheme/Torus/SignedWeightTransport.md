# Signed coordinate weights on an arbitrary split torus

This internal prerequisite transports an integral basis and its signed-weight
count from a coordinate split torus to an isomorphic commutative group scheme
`S`. It takes an actual isomorphism of the underlying group schemes and does
not assume a description of the rational points of `S`.

`characterEquiv e` first interprets an integer coordinate vector as a character
of the coordinate split torus, using `splitTorus.characterLatticeEquiv`, and
then pulls it back along `e` using `characterLattice.comapIso`. Both maps are
integer linear equivalences. `latticePairing_characterEquiv` says that the
pairing with a cocharacter of `S` is the pairing with its composite into the
coordinate torus. The proof is associativity of actual morphism composition,
followed by the published definition of the pairing as the integer exponent of
an endomorphism of the multiplicative group.

`pairingFunctional e ν` is this pairing as an integer linear functional on
coordinate weights. `characterBasis e b` maps an integral coordinate basis
through `characterEquiv e`; as a basis it is linearly independent over the
integers. `characterBasis_detects_cocharacters` proves that vanishing of the
pairing on this basis forces the cocharacter to vanish. Basis extensionality
first makes the pairing vanish on every character. The transported cocharacter
then vanishes by the published perfect pairing for the coordinate split torus.
Composing with the inverse of `e` gives the asserted equality on `S`.

`finrank_eq_signed_card_add_residual` assumes an independent decomposition into
subspaces over a division ring, a finite support whose nonzero part is exactly
the signed vectors of the coordinate basis, multiplicity one at all these
weights, and spanning of the ambient vector space. It applies
`SignedWeightCount.finrank_biSup_eq_signed_card_add_zero` to
`pairingFunctional e ν`, and then replaces the zero-space dimension by
`SignedWeightCount.finrank_zero_eq_sub`. The result counts the signed pairs
using the actual characters of `S`, and contributes the ambient dimension
minus twice the number of basis vectors precisely in degree zero.

The provenance is internal: this is transport of the published actual lattice
maps, the perfect coordinate-torus pairing and the elementary signed dimension
count. The decomposition and multiplicity hypotheses remain explicit; this
module does not establish them for an isometry group. No hypothesis restricts
the characteristic or cardinality of the base field.

The additive equivalence underlying `characterEquiv` is the same one used by
`PointedCoordinateWeights.characterEquiv` in
[PointedCoordinateDecompositionProof](../Rational/PointedCoordinateDecompositionProof.md).
The present declaration retains its integer-linear equivalence type, which is
different from that additive interface.
