# Comparing two tensor functionals on individual slices

Start at a tuple where the first multilinear functional has nonzero value.
The comparison on each fixed-context slot gives the same scalar when
changing that coordinate. To propagate through a finite collection of
coordinates, use induction. If the first functional vanishes at the next
proposed base tuple, add the original coordinate to the proposed one.
Linearity keeps the resulting base value nonzero. Comparing both that sum
and the original coordinate, then subtracting, gives the desired value.

For a tensor product with a separate linear factor, choose a pure tensor
where the first functional is nonzero. The comparison on the separate
factor fixes the scalar for its entire slice. Apply the multilinear
comparison at every separate-factor value where the base tuple remains
nonzero. If a separate-factor value has zero base value, add the chosen
base vector and use linearity. Pure tensors generate the tensor product,
so the comparison holds on the whole space.

This algebraic lemma is used with finite and archimedean local
Whittaker uniqueness on each fixed-context slice in Shalika (1974),
Theorem 5.5.
