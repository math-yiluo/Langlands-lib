# One full root datum over an arbitrary connected base

This internal construction globalizes the actual full coordinate root
datum of a supplied split fibrewise maximal torus in a reductive group
over an arbitrary connected scheme. The base need not be affine and no
Picard hypothesis is needed for the root-datum conclusion.

Realization at a field-valued point transports along a full equivalence
fixing both coordinate lattices. Two data realized on the same field fibre
admit such an equivalence: fibrewise maximality gives maximality of the
canonically normalized torus on that actual field fibre, and the published
field root-datum uniqueness theorem supplies the comparison.

`isGlobalCoordinateRootDatumOf_of_connected` starts with a finite reduced
datum realized on one field fibre. Its open-neighbourhood realization
locus is open and nonempty. The arbitrary-base neighbourhood theorem
supplies a locally common datum near every base point. If such a
neighbourhood meets the realization locus, compare the two data over the
residue field of an intersection point. The resulting identity-lattice
equivalence transports the chosen datum throughout the neighbourhood.
The complement is therefore open; connectedness makes the nonempty clopen
locus the entire base.

`exists_globalCoordinateRootDatumOf_of_connected` chooses an initial
datum near a base point and applies this propagation theorem. The
conclusion quantifies over all actual field-valued points with their
original structure maps, retaining the entire character and cocharacter
coordinate lattices, including central directions.

`globalCoordinateRootDatumOfConnected` is the concrete chosen-data construction supplied by these
existence lemmas. It uses classical choice on the proved existence result;
the preceding lemmas state and prove its mathematical existence and scope.
