# Character-coordinate input for component centralizers

Worker 634.

`RootComponentCoordinates M` is a generic integral input for a supplied affine
pinned model. It consists of a linear equivalence from the full character
lattice to integer coordinates indexed by the simple roots, a Cartan-component
label for each root, support of each root in the coordinates of its label,
and agreement of the labels on simple roots with the actual Cartan diagram.
There is no simply connected or adjoint hypothesis in this structure.

For each component, restriction to the complementary coordinates has an
explicit integral right inverse obtained by extension by zero. A root has
zero restriction exactly when it belongs to the selected component. One
direction is the supplied support condition. Conversely, a zero restriction
for a root in another component would make all of its coordinates zero;
injectivity of the full coordinate equivalence contradicts the nonzero root.

For an `AffineSimplyConnectedPinnedModel`, the simple-coroot pairing
coordinates construct this generic input. Their support property follows from
the coroot-component support theorem and symmetric vanishing of Cartan
pairings. Other constructions of the same integral coordinate input may be
used for other classes of pinned models.

The structure and results are internally derived interface material for the
component-centralizer proof route motivated by Conrad, *Reductive group
schemes* (2014), Proposition 6.4.4, pp.232–233. This module defines and verifies
the lattice input; it does not yet prove almost simplicity, normality, or a
product isomorphism for derived centralizers.
