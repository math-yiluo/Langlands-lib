# Transport of prescribed field-point image lifting

Author: Worker 620.

This internal prerequisite isolates image lifting for the actual strong maps
used to define localized étaleness and proves its transport to arrows of the
analytic étale site. The strong lifting proposition and localized right
cancellation remain explicit assumptions.

`StrongEtaleFieldPointImageLiftStatement` uses the independent ground-field,
space and extension-field universes `u`, `v`, and `uL`. It quantifies over
complete ultrametric ground fields `K`, complete algebraically closed
ultrametric fields `L` with `NormedAlgebra K L`, presentations `A` and `B`,
and an all-pieces étale strong map between their constructed saturations.
Every full `L`-valued point of the target whose ordinary point is in the image
must lift to a full `L`-valued point of the source with exactly the prescribed
image. This proposition is not proved in this module.

The private categorical lemma transports image lifting relative to a natural
transformation between two type-valued functors along an isomorphism in the
arrow category. The inverse source and target maps transport the ordinary
image witness and prescribed point to the original arrow. Naturality gives
the image-membership hypothesis there. After lifting, the forward source map
gives a lift for the new arrow; the commuting square and inverse identities
prove equality with the original prescribed point.

`exists_localized_fieldPoint_lift_of_strong` applies this argument to
`localizedFieldPointFunctor`, the lifted ordinary-point functor, and
`localizedFieldPointProjection`. The definition of `etale` supplies the
required all-pieces étale strong map and arrow isomorphism. The strict descent
identities identify image lifting for its localized image with the assumed
strong lifting statement. The conclusion preserves the entire field point,
including its chart evaluations.

`EtaleSite.geometricPointImageLift_of_strong` additionally assumes right
cancellation for the actual localized étale predicate, universally in `K`.
For a site arrow `f : V ⟶ U`, its equation
`f.left ≫ U.hom = V.hom` and étaleness of both structure maps give étaleness
of `f.left`. The preceding transport theorem then proves the published
`GeometricPointImageLiftStatement`, conditionally on the two stated inputs.

The provenance is internal: the proof uses only the existing definition of
localized étaleness, the actual field-point descent and projection, naturality,
arrow-isomorphism identities, and the over-category equation. It adds no
analytic identification, Hausdorff assumption, or nontrivial valuation
assumption. It does not prove strong image lifting, right cancellation, the
other finite-diagram inputs, or `GeometricPointStatement` unconditionally.
