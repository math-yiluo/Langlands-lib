# Comparisons of supplied root-filtration models

This internal supporting unit compares actual supplied models of one relative
root subgroup. It constructs no root models and proves no special-fibre kernel
geometry. The homomorphism-extension criterion remains an explicit premise.

For a supplied apartment, a reference point, one relative root and arbitrary
real depths, `RootFiltrationModelData.genericIso` identifies the generic groups
of two supplied models through their representations of the same all-test root
subgroup functor. `genericIso_hom_comp` proves compatibility with their actual
inclusions into the ambient group.

`map_mem_integralPoints_of_depth_le` takes depths `r ≤ s` and a generic map
from the depth-`s` model to the depth-`r` model that commutes with their root
inclusions. It proves that this map preserves integral points. The proof uses
the exact integral-point images in `RootFiltrationModelData` and the actual
filtration's antitonicity. Monomorphy of the shallower root inclusion then
identifies the point obtained from its image with the image under the specified
generic map. No equality of chosen root representatives is required.

`comparisonHom` applies the explicit `IntegralModel.HasSmoothHomExtension`
criterion to the canonical generic isomorphism, the smooth deeper model and
the preceding point-preservation result. It is a compatible integral-model
homomorphism from the deeper model to the shallower one.

`comparisonHom_comp` compares this map with arbitrary compatible root maps
into two ambient models and an ambient map extending the generic identity.
Both composites have the same generic restriction by the compatibility laws
and `genericIso_hom_comp`. Generic rigidity for the actual flat affine integral
models proves equality of the integral composites.

These constructions are derived from the published representability,
root-filtration and integral-model interfaces. They form a comparison input to
the host kernel argument; neither the extension criterion nor any unproved
kernel statement is established here.
