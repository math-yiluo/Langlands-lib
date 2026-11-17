# Positive-weight coordinates of actual contracting points

This derived unit strengthens the existing supplied-cell coordinate theorem to
allow nonpositive weights on the negative root list. It assumes an actual open
cell, root maps equivariant for a supplied coordinate torus, and a cocharacter
whose pairing with every negative-list character is at most zero.

For every commutative test ring, an actual point of the cocharacter's dynamic
contracting subgroup has a unique ordered positive-list coordinate vector.
Every coordinate whose character has nonpositive weight vanishes. The selected
vector is `positiveWeightCoordinates`; reconstruction, uniqueness and the
vanishing assertion are proved in the module. No strict positivity assumption
on the positive list is required for this direction.

The implemented proof adapts `SplitBorelPositiveCoordinates`' local-ring
argument. An orbit extension specializes to one at zero; the local ring of the
line at zero puts the extension in the open cell, and its generic closed-fibre
point lets one conjugate back to obtain a cell lift of the original point.
For a nonpositive weight, inverse conjugation multiplies the extension's
coordinate by a nonnegative power of the line parameter. Evaluation at zero
kills that coordinate because the extension specializes to one, even if that
power is zero. The same argument kills all nonpositive coordinates in the
positive list. The torus coordinate is one as in the existing proof.

The arbitrary-ring argument localizes at every prime to obtain a lift through
the open immersion, then reflects coordinate vanishing and torus triviality
from those localizations. Thus nilpotents, disconnected rings and the zero
ring are included. This is a consequence of the existing actual dynamic and
cell interfaces; it is not a new translation of original literature. The unit
does not prove that the supported products contract, nor construct or descend
a filtration.
