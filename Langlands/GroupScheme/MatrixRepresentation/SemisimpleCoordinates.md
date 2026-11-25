# Coordinates for simple stable subspaces and semisimple decompositions

`StableSubspaceRepresentation` records actual finite matrix representation
coordinates for a supplied subspace: a dimension, representation, injective
intertwining inclusion matrix, and equality of its range with the subspace.
Every stable subspace of an actual representation of an affine group scheme has
such coordinates. The construction chooses split matrix coordinates, restricts
the actual representation to those coordinates, and uses the all-affine-test
stability condition to prove invariance.

For a simple stable subspace these coordinate representations are irreducible.
The nonzero range makes their coordinate space nontrivial. Any stable subspace
in the coordinate representation has a stable image in the original one;
minimality and injectivity make it either zero or the whole coordinate space.

The finite independent simple-subspace decomposition from
`AffineSemisimpleModules` therefore gives a finite family of irreducible actual
representations. Their inclusion matrices concatenate to an actual intertwiner
from their direct sum to the given representation. Independence makes this
matrix injective, and the spanning condition makes it surjective.

This is derived coordinate linear algebra over any field, with no smoothness,
reducedness, finite-type, or highest-weight hypothesis. The affine-group
hypothesis is used in the stable-coordinate restriction and operator-module
decomposition. The module supports semisimple descent for
`SplitHighestWeightBaseChangeStatement` but does not
assert descent or classification.
