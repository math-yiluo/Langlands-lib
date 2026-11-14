# All-test commutation from bounded rational split-torus points

This internal derived module defines `KernelPointwiseCommute v i j`: every
rational point of the first group commutes, in the ambient group, with every
rational point in the character-valuation kernel of the second group.

If both groups are split tori, the ambient scheme is affine, and the residue
field of the supplied valuation is infinite, this rational condition implies
commutation over every test scheme. The proof compares the two multiplication
maps from the product of the split tori into the ambient group. Projection from
the product preserves the character-valuation kernel, so the assumed rational
commutation equates those maps on the product kernel. The function-detection
result in `SplitTorusBoundedDetection` makes the two maps equal. Pulling this
equality back along a pair of arbitrary test points gives their commutation.

For a commutative second group, the final theorem packages this conclusion as
containment of the first image functor in `torusCentralizer j`. It verifies the
centralizer condition after every refinement of an arbitrary test scheme. The
module supplies an internal bridge for the descended-apartment torus inclusion;
no additional theorem is attributed to external literature.
