# Coherent comparisons between recovered component models

This internal result supplies actual comparison maps between recovered full and
neutral integral models. The unramified smooth Hom-extension assertion remains
an explicit premise. It neither proves that assertion nor constructs any
upstairs building model or residue geometry.

Work over a nonarchimedean local field `F` in arbitrary universe `u` and either
characteristic. Let `K` be the actual inertia fixed field and `A` its integers.
For `i = 0, 1`, let `Dᵢ` be downstairs component-model data and `Eᵢ` upstairs
component-model data. A supplied `UnramifiedComponentModelRecovery Dᵢ Eᵢ`
recovers both actual models over the identity of the original generic group,
with the pulled-back inclusion square.

`UnramifiedComponentModelComparisonStatement` says that, conditional on
`UnramifiedSmoothHomExtensionStatement`, every supplied actual comparison from
`E₀` to `E₁` has a unique downstairs full and neutral comparison from `D₀` to
`D₁`. Its coefficient pullback commutes with both recovery isomorphisms and the
original upstairs full and neutral maps. The theorem
`unramifiedComponentModelComparison` proves this precise assertion.

The proof first extracts inclusion of the supplied full integral-point images
from the upstairs comparison. The recovery isomorphisms turn it into inclusion
of the integral-point images of the unramified base changes of the downstairs
full models. The explicitly assumed Hom-extension assertion extends the generic
identity to an actual downstairs full-model map. `RelativeComponentModelHom.ofFull` restricts
this map to the actual relative components and gives their inclusion square.

Published flat-affine generic rigidity makes each model map with a fixed generic
map unique. Consequently a full and neutral comparison package is a
subsingleton. Both composites in each recovery square are compatible model maps
over the same generic identity, so generic rigidity makes them equal. This
proves recovery of the original upstairs maps and uniqueness of the complete
comparison, independently of choices of downstairs presentations.

The helper `nonempty_identityHom_iff_unramified_integralPoints_le` states the
exact conditional image-inclusion criterion for generic-identity maps between
arbitrary downstairs integral models with smooth source. Its forward direction
uses published necessity of integral-point preservation; its reverse direction
uses the assumed Hom-extension assertion. For recovered component data,
`nonempty_comparison_iff` transfers this criterion to the supplied full image
subgroups. `nonempty_neutralHom_iff` does the same for the actual neutral-model
maps using smoothness of the neutral source.

`Hom.baseChangeIdentity` is the actual coefficient pullback of a generic-identity
model map, with the generic identity normalized by functoriality. This retains
the literal pullback as its underlying map, so the two recovery squares concern
actual maps, rather than only their integral-point actions or special fibres.

The provenance is an internal deduction from published coefficient pullback,
integral-image necessity, generic rigidity, relative-component restriction and
the recovery interface. Every model and recovery isomorphism is supplied. No
special-fibre kernel, parabolic correspondence, torus lift or special apartment
is constructed. The host prescribed-point split-torus theorem remains open.
