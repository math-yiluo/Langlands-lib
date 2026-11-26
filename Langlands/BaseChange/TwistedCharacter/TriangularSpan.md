# Separation of spans from leading character lines

Suppose a family of independent vectors is indexed by a set with a rank
function to a linear order. For each index in a selected subset, take a
vector whose expansion has a nonzero coefficient on its indexed line
and all remaining terms of strictly lower rank. The span of the new
vectors is disjoint from the span of the original lines indexed by a
disjoint subset.

The coefficient map of the independent family extends to the ambient
space by a left inverse to the finite linear combination map. In a
nonzero finite combination of the new vectors, choose an index of
maximal rank with nonzero coefficient. Its coordinate in the sum is
the product of that coefficient and the nonzero leading coefficient.
Every other summand has zero contribution at that coordinate. The
span of the disjoint set of original lines has zero at the same
coordinate, so the sum cannot lie in that span.

This is the linear algebra needed to separate twisted standard traces
from irreducible twisted character lines indexed by different heads.
For the standard-module basis used in Henniart–Lemaire (2011),
II.5.10–II.5.11, the leading line comes from the irreducible Langlands
head. A rank function with strict descent on the head-kernel terms
supplies the triangularity hypothesis.
