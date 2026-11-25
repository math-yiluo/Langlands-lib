# The convolution group of Hopf algebra points

Algebra maps from a Hopf algebra `H` to a commutative semiring form a group under convolution. The inverse of a point is its composite with the antipode. The antipode takes values in the opposite algebra, and commutativity of the target lets the point factor through that opposite algebra. The inverse law follows by postcomposing the linear convolution identity for the antipode with the given point.

For a bialgebra, postcomposition with an algebra map gives the monoid homomorphism `AlgHom.mapValue` on points. Its evaluation lemma exposes ordinary composition, and Mathlib's convolution formula proves multiplicativity.
