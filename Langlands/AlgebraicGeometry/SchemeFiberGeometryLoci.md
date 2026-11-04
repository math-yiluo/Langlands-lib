# Actual geometric fibre loci

This is a derived construction for the last fibre-property clause of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It constructs the actual target subsets needed for a later
constructibility and filtered-descent argument.

For any scheme morphism f, `nonemptyFiberLocus f` consists of target
points whose actual residue-field fibre is nonempty;
`geometricallyConnectedFiberLocus f` requires that fibre's structure
morphism to its actual residue-field spectrum to be geometrically
connected; `pureDimensionFiberLocus d f` requires every irreducible
component of that fibre, with its inherited topology, to have
Krull dimension d. The combined
`nonemptyGeometricallyConnectedPureDimensionFiberLocus d f` retains all
three explicit conditions. No finiteness or separation assumption is
imposed, and an empty fibre satisfies only the dimension condition
vacuously.

The nonempty locus is the actual image of f, proved using the
homeomorphism from a scheme-theoretic fibre to the inverse image of
its target singleton. Mathlib's convention that connected spaces are
nonempty makes the geometric-connectedness locus a subset of the
nonempty locus. Thus the combined locus equals the intersection of the
geometric-connectedness and pure-dimension loci. Fullness of each of
these three loci is equivalent to its corresponding published
all-fibres predicate. These are exact comparisons of the actual sets,
without a chosen auxiliary presentation.

For any cartesian square and any point y of its new target, the
actual fibre comparison is cartesian over the actual residue-field
extension. The map of spectra of that extension is surjective: its
source is nonempty and its target has one point. Surjectivity of the
map from the new fibre to the original fibre follows by base change.
This proves preservation and reflection of fibre nonemptiness.
For geometric connectedness, preservation is Mathlib's stability under
base change and reflection reuses the published Library adapter
`Langlands.AlgebraicGeometry.geometricallyConnected_of_surjective_isPullback`
from `GeometricallyConnectedDescent`. Applying these pointwise
comparisons gives equality of each of these two loci with the inverse
image of the original locus. These equalities hold for arbitrary
scheme morphisms and arbitrary cartesian presentations in a common
arbitrary universe.

This module establishes no constructibility result, no pure-dimension
base-change equality and no filtered-descent theorem. Those are
separate proof obligations; the unrestricted actual-model target
remains `FinitePresentationInitialRingFiberGeometryDescent`.
