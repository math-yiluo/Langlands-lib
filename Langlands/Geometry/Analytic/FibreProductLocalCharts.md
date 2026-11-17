# Locally Hausdorff gluing and embedded local pair charts

This internal construction concerns the actual unrestricted fibre-product
pair-chart quotient. It assumes no global Hausdorffness. The field, space
and atlas-index universes remain independent.

`goodPairs` selects original pairs whose two factor chart ranges lie in
open Hausdorff factor patches. It is downward closed. The base is not part
of this selection: embedding these charts needs only the factor patches.
`exists_goodPair_neighborhood` uses rational-domain refinement and factor
domain saturation to find a selected subpair whose actual spectrum
restriction image is a neighborhood of any specified original spectrum
point. It asserts a neighborhood in spectrum coordinates, with no claim
that a single chart is a neighborhood in the ambient analytic space.

`isEmbedding_goodChart` first embeds the selected spectrum as a closed
chart of the factor-patch quotient. That quotient embeds openly in the
unrestricted quotient by the saturated open-subsystem theorem. Composition
therefore embeds the actual original pair chart. This argument requires
factor saturation and does not use a compact-injective-map argument in a
locally Hausdorff codomain. The actual images of good pairs cover the full
quotient (`subsystemSupport_goodPairs`) by the neighborhood refinement and
the original restriction/gluing identity.

`exists_hausdorff_patches` chooses open Hausdorff neighborhoods of the two
factor images and their common base image, then intersects the factor
neighborhoods with the inverse image of the base neighborhood. The quotient
square identifies the common base point. The resulting open Hausdorff
factor patches have images in the same open Hausdorff base patch.

Under saturation of all three atlases, `locallyHausdorff_chartSystem`
applies the proved Hausdorff patch-quotient result to these neighborhoods.
The patch quotient embeds openly into the full quotient, and its image is
a neighborhood of the original point with Hausdorff subspace topology.
Thus the unrestricted actual gluing is locally Hausdorff.

`goodChartFamily` is the family of nonempty actual ranges of good pair
charts. This module does not yet prove that family is a net or construct
the final analytic atlas. The same-universe object, categorical universal
property and etale base change remain further work. No external statement
is transcribed.
