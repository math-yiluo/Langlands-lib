# Independence of the representative in the actual root-point Lie comparison

This internal deduction proves independence of the affine representative used
by the root-point comparison. It retains an arbitrary field, arbitrary common
universe and arbitrary characteristic. The ambient group is smooth and affine,
and the given split-torus character is nonzero and has no higher positive roots.
No reductivity or root occurrence is required.

`rootSubgroupRepresentativeIso` specializes the canonical represented-subgroup
isomorphism to any two group schemes representing the same intrinsic root
subgroup. It commutes with their inclusions. Postcomposing with the
second monomorphic inclusion shows that this isomorphism intertwines the actual
torus actions (`subgroupAction_isoOfIsRepresentedBy`). The companion point
formula `pointsEquiv_isoOfIsRepresentedBy` shows that corresponding represented
points give precisely the same point of the original subgroup functor. These
two preliminary facts hold over an arbitrary base scheme.

`representedRootPointLieEquiv_eq` compares the two constructed additive
equivalences with the actual adjoint weight space. Each representative has
natural coordinates of the original nonzero weight. The imported equivariant
isomorphism naturality identifies their point-to-Lie comparisons through the
actual differential of the canonical isomorphism. Naturality of the rational
versus coefficient point convention and the equality of the representing
inclusions then give equality of the ambient Lie vectors. Subtype
extensionality gives equality in the original weight space.

`rootPointLieEquiv_eq_represented` uses the representative specification in
`rootPointLieEquiv_exists_representative` and this independence theorem. Thus
the intrinsic comparison agrees with the comparison through every affine
representative, including its independently chosen weight coordinates.

The provenance is an internal deduction from actual represented-subgroup
isomorphisms, root weight coordinates and point-to-Lie isomorphism naturality.
This module does not yet prove Galois compatibility or identify restriction
fibers, fixed-field coordinates, root valuations or apartments.
