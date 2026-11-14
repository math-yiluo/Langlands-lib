# Lie images for homomorphisms with smooth scheme-theoretic kernel

This internal derived unit compares the two actual Lie images that occur
when a homomorphism is replaced by its schematic image. It uses the existing
`SchematicImage` construction and the actual dual-number identity kernels.

Let `f : H → G` be a homomorphism over an arbitrary field `k`. Assume that
`H` is smooth, connected and affine, and that `G` is affine and locally of
finite type. `SchematicImage.isFppfQuotient_projection` proves that the
canonical projection onto the schematic image is an fppf quotient by the
full scheme-theoretic kernel of `f`. The proof uses the published flatness,
surjectivity and finite-presentation results in `HomImage`. Since the image
inclusion is a monomorphism, its postcomposition preserves the complete
kernel subgroup functor.

`SchematicImage.smooth_projection_of_smooth_kernel` adds the hypothesis
that this full kernel is smooth. The published represented-kernel fppf
quotient theorem then proves that the canonical projection is smooth.

`Lie.range_schematicImage_inclusion_of_smooth_kernel` states equality of
the differential image of `f` with the differential image of the closed
schematic-image inclusion. It holds over every commutative coefficient
`k`-algebra `A`, at the actual epsilon-scaling linear maps. Smoothness
of the projection makes its differential surjective by the published
`Lie.targetMapLinear_surjective_of_smooth`. The canonical factorization of
`f` then gives both range inclusions. `SmoothKernelSchematicLieImageStatement`
packages this equality at arbitrary universe `u`, and
`smoothKernelSchematicLieImage` proves that proposition.

Smoothness of the full kernel is an essential hypothesis. The result does
not infer it from smoothness of the source or schematic image, or from
connectedness or unipotence of a reduced kernel. It makes no characteristic
restriction.

The motivating consumer is the computation of Lie weights of the schematic
image of an integral-model comparison in a special-fibre quotient. This
unit supplies a geometric comparison once that composite's full kernel is
proved smooth. It supplies neither the kernel smoothness for that consumer
nor its root-filtration calculation or facet sign formula. All assertions
are derived from the existing Library theorems named above; no additional
source theorem is asserted.
