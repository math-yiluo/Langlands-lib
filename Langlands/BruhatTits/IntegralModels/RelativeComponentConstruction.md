# Relative-component model data from a smooth affine integral model

This internal construction packages published relative-component results into
`RelativeComponentModelData R K G`. Its input is an actual smooth affine
integral model `M` over any DVR `R`, with fraction field `K`, and geometric
connectedness of the original generic group `G`. It constructs no full model
from a subgroup of `G(K)` and identifies no neutral integral-point subgroup.

`relativeComponentModelDataOfSmooth` uses the proved
`RelativeIdentityComponent.smoothExistence` to choose a smooth geometrically
connected relative component `i : H → M.group`. The proved
`smoothDvrAffineness` makes its actual structural morphism affine. Smoothness
supplies flatness and local finite type. Base change of the represented
component to `K` is the relative identity component of the actual generic
fibre of `M`. That generic fibre is geometrically connected, transported
through the original generic isomorphism of `M`, so its identity morphism
represents the same all-test condition. Uniqueness of representatives gives
the generic isomorphism for `H`. Its composite with the original generic
isomorphism identifies the neutral model with exactly the original `G`.
The uniqueness comparison equation proves that the model inclusion extends
the identity of that original `G`. The full model remains literally `M`.

The two helper lemmas prove the all-test identity criterion for any group
scheme with geometrically connected fibres, and transport geometric
connectedness through the supplied generic isomorphism using its cartesian
square over the identity base map.

This is derived content from the imported Library APIs. Its intended use in
KP Theorems 8.3.2 and 8.3.13 is limited to assembling the models after existence
of a smooth full model has been proved. The separate equality between the
neutral integral points and `G(K)^0` intersected with a building fixer remains
an additional mathematical obligation. No uniqueness of full models is
asserted.

The `OfSmooth` name distinguishes this choice-based constructor from
`IntegralModel.relativeComponentModelData` in
`GroupScheme/IntegralModel/RelativeComponentConstruction`, which takes a
supplied relative-component inclusion and its geometric witnesses. Both
constructions retain their original inputs and outputs.
