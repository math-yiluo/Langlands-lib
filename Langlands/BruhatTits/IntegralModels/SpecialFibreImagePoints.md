# Rational lifts through special-fibre schematic images

This internal derived module proves that the actual schematic-image projection
is surjective on rational points over a perfect field when the original
homomorphism has smooth connected unipotent full kernel. The specialization
`RelativeComponentModelHom.specialFibreImageProjection_surjective` supplies a
geometric input to the reduction-preimage criterion for KP model morphisms.
It assumes `HasSmoothConnectedUnipotentKernel`; it does not prove that clause,
parabolicity of the image, or the facet-specific congruence containment.

The proof uses existing Library theorems, without an additional literature
assertion. First, `kernel_range_imageProjection` uses the monomorphism from the
schematic image into the original target to identify both full kernel range
functors on every test scheme. For a smooth affine source and an affine target
locally of finite type, the image is smooth (`HomImage.smooth_image`), its
projection is faithfully flat (`DominantHom.flat_surjective`), and that
projection is locally of finite presentation. Thus
`isFppfQuotient_imageProjection` identifies the original schematic-image
projection as the represented fppf quotient by the original full kernel.

Over a perfect field, `perfectFieldUnipotentSplit` makes the smooth connected
unipotent kernel split. Applying
`HomogeneousQuotient.fppf_section_of_split_unipotent_torsors` with the proved
`splitUnipotentAffineTorsorStatement` gives a section of the underlying scheme
map of the image projection, recorded in
`exists_unipotentKernelImageSection`. The definition
`unipotentKernelImageSection` chooses this section, and `unipotentKernelImageSection_comp` proves its right
inverse identity. Composing a rational point of the image with this section
proves `rationalPoints_imageProjection_surjective_of_unipotent_kernel`.
The chosen section need not be a group homomorphism.

The model specialization uses the smooth neutral source and the affine,
finite-type neutral target already included in `RelativeComponentModelData`.
Their actual residue-base changes inherit these properties. No Henselian
hypothesis is needed for this special-fibre result. The arbitrary universe
`u` is retained. All image objects and maps use the published `SchematicImage`
construction appearing in `SpecialFibre.lean`.
