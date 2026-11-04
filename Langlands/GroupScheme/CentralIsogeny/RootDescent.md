# Termination of characteristic division of split-torus roots

This internal supporting unit proves
`SplitRootDivisionTerminationStatement.{u}`. Fix a split torus over a
field of positive characteristic `p > 1`, and any family of affine
locally finite type group schemes over that field. Suppose every map
from the fixed torus to a member of the family admits a central
isogeny to another member whose composite kills every source tangent
vector. Then the actual adjoint root support of every such map is empty.
The family may be infinite, and its index type may lie in `Type (u + 1)`.
The supporting theorem also allows an arbitrary independent index universe.

The proof collects all roots of all torus maps into a single set of
characters of the same fixed torus. Zero is absent by the definition of
roots. The theorem `IsCentralIsogeny.exists_divided_root` supplies, for
each member of this set, another member whose `p`-multiple is the
original character. This uses the actual root preservation theorem for
central isogenies and the actual factorization of a zero-differential
split-source map through multiplication by the characteristic.

The arithmetic argument does not assume that this set is finite.
For any additive map from its character lattice to the integers,
strong induction on the absolute value of a coordinate proves that
the coordinate vanishes on the whole set. Otherwise, division by
`p > 1` gives another nonzero coordinate of strictly smaller absolute
value. An actual splitting isomorphism of the source identifies its
character lattice with a finite product of copies of the integers.
The preceding conclusion for each coordinate says every character in
the set is zero, contradicting the exclusion of zero.

These are internal deductions from the imported character lattice,
root restriction and central-isogeny constructions. The unit does not
construct the required outgoing isogenies, nor assert that a composite
of central isogenies is central. Those are separate host obligations.
