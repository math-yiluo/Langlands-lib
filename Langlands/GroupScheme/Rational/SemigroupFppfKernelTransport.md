# Semigroup transport with contained full kernel

Worker 1372. This is an internal deduction and construction from the published
semigroup realization, functoriality, split-torus weight decomposition,
full-Lie open-subgroup criterion and fppf subgroup descent. It applies over
any field in arbitrary universe. The source and target groups are smooth and
affine, the acting group is a split torus, and the ambient homomorphism is
equivariant on every test scheme.

`actionWeightSupport_comap_semigroup_subset_of_kernel_le` bounds the weights
of the full inverse image of the target semigroup subgroup. Its assumptions
include the exact semigroup Lie images on source and target and containment
of the entire actual kernel in the source semigroup subgroup. An excluded
weight vector maps into both its target weight space and the target
semigroup weight span. Their disjointness makes its image zero. The original
dual-number point therefore belongs to the full kernel, hence to the source
semigroup subgroup. The source exact Lie image and weight disjointness force
the original vector to vanish. For any represented stable inverse image,
`hasLieImage_comap_semigroup_of_kernel_le` converts this support bound into
tangent containment by the split-torus decomposition. Functoriality gives the
reverse containment. Published realization supplies the two exact Lie images
and stability, so the inverse image and source semigroup subgroup have the
same actual Lie image.

`isFppfImage_semigroup_of_kernel_le` assumes the ambient homomorphism is flat,
surjective and locally of finite presentation, with the full kernel
containment just described. Choose smooth connected closed representatives
of both semigroup subgroups. The actual pullback of the target representative
is affine and locally of finite type. It represents the full inverse image,
without initially requiring that inverse image to be smooth or connected.
Functoriality gives the closed inclusion of the source representative into
this pullback. Equality of their actual Lie images makes this inclusion full
on the Lie algebra, and the published full-Lie criterion makes it an open
immersion. Its composite with the pullback projection to the target
representative is flat and locally of finite presentation. The smooth
connected affine target representative is geometrically integral and thus
irreducible. The published surjectivity theorem for flat homomorphisms onto
irreducible groups makes this composite scheme-surjective. These actual maps
witness `SubgroupFunctor.IsFppfImage`.

`semigroup_comap_eq_of_fppf_of_kernel_le` applies published fppf descent with
the full kernel containment to obtain equality of the entire inverse-image
functor and the source semigroup subgroup. Every equality and containment
uses arbitrary scheme tests; it is not restricted to field points.

`semigroupFppfRestriction` is the canonical actual homomorphism on any supplied
representatives of the two semigroup subgroup functors. It specializes the
published `IsRepresentedBy.restrictionHom` using the new full inverse-image
equality. Its composite with the target inclusion is the source inclusion
followed by the ambient homomorphism. The published cartesian-restriction API
then proves that its square is cartesian on schemes. Pullback stability gives
its flatness, scheme surjectivity and local finite presentation. No new generic
restriction construction is introduced.

The full kernel containment is an explicit essential hypothesis. No smoothness
is required of the ambient homomorphism or of its full kernel, and no
restriction on whether zero belongs to the semigroup is imposed beyond that
containment. This module does not itself establish that containment for
adjoint quotients or prove the unconditional host semigroup comparison.
