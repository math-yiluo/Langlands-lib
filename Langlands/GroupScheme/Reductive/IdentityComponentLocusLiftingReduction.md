# Openness reduced to exact relative torus lifting

The selected definition
`identityComponentReductiveNeighbourhood_of_lifting` constructs an actual
open neighbourhood at every point of the unchanged reductive geometric
identity-component locus of a smooth affine group scheme over an arbitrary
scheme. The only retained universal structural premise is
`RelativeSplitTorusLiftingStatement`. The theorem
`identityComponentReductiveLocusOpen_of_lifting` concludes the exact
`IdentityComponentReductiveLocusOpenStatement` from that premise, uniformly
in the arbitrary universe `u`.

The affine constructor
`splitTorus.identityComponentReductiveNeighbourhood_intrinsic` starts with
a supplied closed standard torus that is self-centralizing in the actual
geometric identity component at the specified original point. Locus membership
makes that actual component connected reductive. The intrinsic reflection
construction provides both negation of the actual exponent roots and the
exact `GeometricRootReflectionData` for each root. The published
`rootReducedness` and `splitRootLieLine` proofs, through their existing
geometric-coordinate and relative-rank adapters, supply equality or opposition
of proportional roots and rank one of the actual relative exponent summands.
The existing finite root-centralizer construction then produces an actual
good open in the original affine base. No family of good opens is assumed.

For an actual maximal torus at an algebraically closed field-valued point,
the published `maximalTorusCentralizer` proof supplies the self-centralization
statement used by the zero-weight comparison. The existing field-point
comparison transfers that zero-weight dimension to the original geometric
fibre's relative rank, establishing exactly the self-centralizing predicate
needed above. This step does not identify independently chosen algebraic
closures.

The extension constructor handles an arbitrary field-valued point by
extending its field to its algebraic closure. The published maximal-torus
base-change proof and the actual pullback-composition and standard-coordinate
isomorphisms preserve maximality. The spectrum of a field has one point, so
the image in the original base is unchanged. The arbitrary-scheme constructor
factors the field point through an affine-cover chart, transports the same
actual torus inclusion through its pullbacks, and applies the affine
constructor there. The open-image descent construction returns a good open
in the original scheme. A split presentation extends this construction from
standard coordinates to any supplied actual split commutative torus.

The constructor for a specified split maximal torus in the canonical residue
fibre applies the retained lifting statement to that exact inclusion. Its
recovery equation, with the actual source and ambient pullback isomorphisms,
preserves maximality in the lifted field fibre. Splitness makes the lifted
group commutative without replacing its underlying group. The equality of
the lifted residue point's composite with the canonical residue point
identifies its image with the original point. The exact base-change equality
for the reductive identity-component locus transfers locus membership, and
the etale open image of the constructed good open returns the required
original-base neighbourhood.

The selected definition constructs its own initial torus. The published
finite-Galois splitting and maximality base-change proofs supply a split
maximal torus after a finite Galois extension of the original residue field.
The prescribed etale residue-extension construction realizes that same field
and scalar map. The actual inverse residue-field comparison and
pullback-composition isomorphism place the torus in the canonical residue
fibre of the pulled-back group, preserving its actual inclusion and
maximality. The preceding lifting constructor gives its good open, which
descends through the etale projection. The pointwise criterion for open sets
then proves the stated conditional universal openness theorem.

The provenance is internal composition, adapting the earlier conditional
neighbourhood assembly by Worker 1621 and Worker 1683 to the intrinsic
reflection construction and the published field proofs. The earlier
conditional constructors remain unchanged. The full-kernel condition and
integral coroot data of the universal field-reflection statement are
unnecessary here.

Relative split-torus lifting remains an explicit unproved input of this
module. Accordingly, this contribution does not prove unconditional openness
or close its proof task. The original base is arbitrary, including
nonreduced and nonnoetherian bases, and the original ambient fibres may be
disconnected. There is no characteristic restriction.
