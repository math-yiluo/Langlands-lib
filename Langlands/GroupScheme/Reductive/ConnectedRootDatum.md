# One full root datum over a connected affine base

This internal result supplies the root-datum constancy step in Conrad,
*Reductive group schemes* (2014), Proposition 6.2.11(2), pp. 210–211.
It concerns an actual supplied split fibrewise maximal torus in a reductive
group over a connected affine base. It does not assert root-line freeness
or a global isomorphism of groups.

`CoordinateRootDatum.exists_identityEquiv_of_commonField` compares two full coordinate data
realized on the same field fibre. Their pairings and roots agree, and their
actual normalizer reflections lie in the finite Weyl image. The published
finite-order reflection comparison identifies coroots, producing a full
equivalence whose two lattice maps are the identity, including central
directions.

`isFibrewiseRootDatumOf_of_connected` starts with a finite reduced datum
realized on one field fibre. Consider the locus of points admitting an
open neighbourhood on every field point of which this datum is realized.
It is open by definition and nonempty by the published root-datum
neighbourhood theorem. Its complement is open: a point has an open
neighbourhood carrying some full datum; if this neighbourhood meets the
first locus, compare the two data over the residue field of an intersection
point and transport along the identity-lattice equivalence throughout the
neighbourhood. Connectedness therefore makes the locus the whole base.
The conclusion retains every supplied field algebra structure.

`exists_fibrewiseRootDatumOf_of_connected` chooses the initial finite
reduced datum near one base point and applies this propagation theorem.
All group-theoretic inputs are published field root-datum existence,
finite Weyl image, and the full local root-datum neighbourhood theorem.
No representation or local-ring hypothesis is added.

`connectedCoordinateRootDatum` is the concrete chosen-data construction supplied by these
existence lemmas. It uses classical choice on the proved existence result;
the preceding lemmas state and prove its mathematical existence and scope.
