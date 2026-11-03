# Character spaces of actual matrix representations

Worker 1228.

This internal construction defines the character spaces of a finite matrix
representation of an affine group scheme over an arbitrary field. A vector
belongs to a character space when the universal affine point acts by that
character's universal unit. Naturality proves the corresponding eigenvector
equation on every affine test algebra, including nonreduced ones.

The previously proved linear independence of character units supplies a field
linear coefficient functional selecting any one character. Applying it to each
coordinate of the universal action gives a linear operator which fixes the
chosen character space and kills every other character space. Applying these
operators to a finite relation proves independence of the character spaces.
There is no hypothesis that their sum is the entire representation, and no
semisimplicity, smoothness or commutativity assumption.

The provenance is an internal derivation from
`CharacterUnits.linearIndependent_unit`, coordinate naturality of actual matrix
representations, and elementary linear algebra. This file does not yet construct
a cancelling vector or a representation with a prescribed kernel.
