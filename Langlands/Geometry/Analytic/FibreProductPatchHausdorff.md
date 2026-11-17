# Hausdorffness of local fibre-product patches

This internal construction uses the actual restricted pair-chart quotients.
The first and second projections take values in the actual factor subspaces,
with their induced topologies. Their continuity follows by composing the
original quotient projections with the continuous subsystem comparison.
Injectivity of that comparison transfers the exact pair-chart image formula
to the restricted quotient.

`exists_finite_pairs_in_open_base` assumes domain saturation of all three
atlases. It needs only the compact images of the specified factor charts to
lie in one open Hausdorff base patch. Their intersection is compact in that
patch and hence compact in the ambient base, where it admits a finite cover
by original charts contained in both chosen original base charts and the
open patch. Pulling these domains back into the specified factor charts
constructs the finitely many pair charts. Their exact image formula proves
the finite-cover equality. The ambient base need not be Hausdorff, and the
two original base charts need not lie in the Hausdorff patch.

`exists_finite_patchPairs` transfers this finite cover into the actual patch
quotient. Every smaller pair remains selected because its factor charts are
contained in the specified factor charts. The subsystem comparison is
injective, so the exact image formula supplies both cover inclusions.

`patchChartFamily` consists of the nonempty ranges of these original pair
charts. It refines the family of preimage intersections of the two actual
factor-subspace chart nets. The finite pair cover gives a finite relative
neighborhood refinement: discard the finitely many closed chart ranges
missing the specified point and use the complement of their union as a
relative open neighborhood. The existing finite-overlap result provides
closedness, requiring only Hausdorffness of the two factor subspaces.

For open factor subspaces, domain saturation supplies their original-chart
nets. The continuous subspace projections pull those nets back, and the
finite local refinement therefore makes `patchChartFamily` a net. Its
members are compact Hausdorff because their actual spectrum charts are
closed embeddings. Their pairwise intersections are compact because the
chart ranges are closed. The quasinet Hausdorff criterion proves
`t2Space_patchSystem`. Thus, when both factor patches are open Hausdorff and
their images lie in one open Hausdorff base patch, the restricted quotient
is Hausdorff. Domain saturation of all three atlases is explicit.

These are local topological constructions with independent field, space and
index universes. No same-universe analytic pullback, localized universal
property or etale base change is asserted here. No external statement is
transcribed.
