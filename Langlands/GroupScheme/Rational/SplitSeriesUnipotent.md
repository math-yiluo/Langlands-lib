# Unipotence of affine groups with a finite Ga-series

This internal adapter proves that the existing finite normal Ga-series
predicate implies the existing coefficient-representation `IsUnipotent`
predicate for affine group schemes over every field in universe `u`.
The statement keeps affineness as an explicit hypothesis.

For a series of length zero, its defining equality between the all-test image
of the identity homomorphism and the bottom subgroup implies that every point
on every scheme test is the identity. `HasSplitSeries.zeroVectorCoordinates`
constructs multiplicative equivalences with additive tuples indexed by `Fin 0`.
The inverse is the identity point, and the maps are natural because their
coordinate index type is empty. This construction works over any scheme base.
It yields `IsVectorGroupOfDimension H 0`; vector-group unipotence then proves
the length-zero case over a field.

For a successor series, write `K` for its given closed subgroup and `V` for
its one-dimensional vector quotient. The closed subgroup of the affine source
is affine, so induction proves its unipotence. The series provides an actual
fppf map to `V` and equality of its scheme-kernel image with the image of `K`
on every scheme test. Both inclusions are monomorphisms; uniqueness of
representatives supplies an actual group-scheme isomorphism between `K` and the
kernel. This transfers affineness and unipotence to that kernel.

The quotient morphism is flat and surjective by the fppf premise. It is
quasi-compact because its composite with the quotient's structure morphism
equals the affine source's structure morphism. Vector-group unipotence supplies
unipotence of `V`. The published `isUnipotent_of_kernel_of_quotient` theorem now
proves unipotence of the source. This finishes the induction without assuming
surjectivity on the point group of every original test.

`IsSplitUnipotent.isUnipotent` unpacks the finite series length.
No perfectness, infinitude or characteristic restriction is imposed. Smoothness,
connectedness and normality in the existing series predicate are preserved;
the proof does not need additional hypotheses of these forms.

The provenance is internal: the construction and induction use the published
series definition, natural vector coordinates, represented-subgroup uniqueness,
affineness under closed inclusions and isomorphisms, and the representation-level
extension theorem. This is a prerequisite adapter for the solvable maximal-torus
conjugacy task. It does not construct the required stable vector subgroup,
linearize an arbitrary torus action, or prove the full conjugacy theorem.
