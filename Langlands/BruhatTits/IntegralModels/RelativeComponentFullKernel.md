# Full and neutral kernels of actual relative-component maps

## Scope and statement

This is an internal supporting result for the prescribed-point split-torus
argument. It composes published Library constructions and does not assert a new
literature transcription. The universe `u` is arbitrary, and no characteristic
restriction is imposed.

`RelativeComponentFullKernelStatement` quantifies over a local integral domain
`R`, its supplied fraction field `K`, a `K`-group scheme `G`, two supplied
`RelativeComponentModelData R K G`, and an actual compatible
`RelativeComponentModelHom source target`. Each datum includes smooth affine
full and neutral integral models, compatible generic identifications, and the
assertion that the neutral inclusion represents the actual relative identity
component. The comparison includes actual full and neutral morphisms with their
commuting inclusion square.

The first conclusion is a group-scheme isomorphism over the residue field
between the neutral and full special-fibre kernels, under the hypothesis that
the full kernel is geometrically connected. The second conclusion transfers
smoothness, connectedness and unipotence of the full kernel to
`HasSmoothConnectedUnipotentKernel`, which concerns the actual neutral map.
The theorem `relativeComponentFullKernel` proves this proposition.

## Implemented proof

For either model datum, `specialFibreMap_mono` first installs geometric
connectedness of its neutral model using the published
`RelativeComponentModelData.neutral_geometricallyConnected`. Base change of the
relative-component criterion identifies its actual residue inclusion as an
open immersion. Its underlying morphism in the category of schemes over the
residue field is therefore a monomorphism.

For `range_neutralKernel_full_eq`, geometric connectedness of the full kernel
lets `RelativeIdentityComponent.factor` factor its entire inclusion through
the source neutral special fibre. This is a factorization of group schemes,
not only of residue-field points. The proof compares the images on every test
scheme over the residue field:

- A section of the neutral kernel maps to a section killed by the full map,
  by the actual commuting inclusion square and `kernelPointsEquiv`.
- Conversely, factor a section of the full kernel through the source neutral
  special fibre. Its image under the neutral comparison becomes the identity
  after the target neutral inclusion. The target inclusion is a monomorphism,
  so the section is already killed by the neutral comparison.
  `kernelPointsEquiv` then lifts it to the neutral kernel.

Thus the neutral kernel followed by the source component inclusion and the
full kernel inclusion have equal `SubgroupFunctor.range` in the full source
special fibre. Both inclusions are monomorphisms. The uniqueness theorem
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` constructs
`specialFibreKernelIsoFull` from these two representatives of exactly the same
all-test subgroup functor.

For `hasSmoothConnectedUnipotentKernel_of_full`, the full source and target
special fibres are affine by base change. The full kernel is affine through
its closed kernel inclusion. Its supplied smoothness implies local finite
type, and affineness gives quasi-compactness. The published
`geometricallyConnected_of_connected` therefore supplies the geometric
connectedness needed for the isomorphism. Finally,
`smooth_connected_unipotent_of_groupIso` transfers all three properties along
that isomorphism. The wrapper theorem applies these constructions to the two
conjuncts of the displayed proposition.

## Actual published inputs

- `Langlands.BruhatTits.IntegralModels.RelativeComponent`: the actual full and
  neutral models, component criterion, compatible generic identification and
  actual residue inclusion.
- `Langlands.BruhatTits.IntegralModels.ModelMorphism`: the actual compatible
  full and neutral maps, `specialFibre_component_comm`, and
  `HasSmoothConnectedUnipotentKernel`.
- `Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality`:
  `RelativeComponentModelData.neutral_geometricallyConnected`.
- `Langlands.GroupScheme.RelativeIdentityComponent.BaseChange`: preservation
  of the actual relative identity-component criterion under base change.
- `Langlands.BruhatTits.IntegralModels.ConnectedFactorization`:
  `RelativeIdentityComponent.factor` and `factor_comp` for a geometrically
  connected source.
- `Langlands.AbelianScheme.Kernel`: actual scheme-theoretic kernels,
  `kernelPointsEquiv` and closedness of the kernel inclusion when the target
  is separated.
- `Langlands.GroupScheme.CentralIsogeny.Basic`: `mem_range_kernelι_iff`.
- `Langlands.GroupScheme.RepresentedSubgroup`:
  `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`.
- `Langlands.GroupScheme.GeometricConnectedness`:
  `geometricallyConnected_of_connected` for finite-type groups over a field.
- `Langlands.GroupScheme.KernelSquareTransport`:
  `smooth_connected_unipotent_of_groupIso`.

The transitive imports use published Library and Mathlib results. The proof
uses none of the barred unramified building-descent statements or their
consumers.

## Remaining host obligations

Full-kernel geometry is an explicit input here. This result proves no
existence of the supplied integral models, no formula identifying neutral
integral points with full norm-one fixers, no parabolic-image assertion, and
no residue-torus lift or maximal split-torus construction. The exact host
`UnramifiedFixedPointSplitTorusStatement` remains open.
