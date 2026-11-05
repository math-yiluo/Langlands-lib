# Rational quotients of represented adelic subgroups

Let `F` be any number field and `j : H ⟶ G` any actual group-scheme
homomorphism over `F`. The subgroup functor `SubgroupFunctor.range j`
means the image on every test scheme. Its evaluations on `F` and the full
adele ring are precisely the images of the corresponding actual point
homomorphisms.

`rationalRangeMap` and `adelicRangeMap` restrict these homomorphisms to those
evaluated image subgroups. The latter is continuous for the canonical
coordinate-evaluation topology on `H` and the subspace topology on the
adelic subgroup of `G`. It is surjective by the definition of the image
functor. `adelicRangeMap_rational` proves compatibility with the actual
principal rational-point maps, using their published naturality.

`representedQuotientMap` therefore descends to a continuous surjection

`H(F) \ H(A_F) → (range j)(F) \ (range j)(A_F)`.

Both sides are the existing actual left homogeneous quotients by principal
images. The representative formula and compatibility with positive right
translation are proved. No monomorphism, affineness, finite-type or
normality hypothesis on `j` is needed for this map, and no injectivity or
homeomorphism is asserted.

`compactSpace_rationalQuotient_range` transfers compactness from the
represented source quotient by taking its continuous surjective image.
`compactSpace_rationalQuotient_range_unipotent` applies this to affine,
smooth, connected, unipotent `H`. It uses the published compact rational
cover theorem with the published perfect-field unipotent-splitting and
split-unipotent affine-torsor proofs. In particular, those structural
inputs are discharged here. The target `G` need not be reductive or
affine, and no measure, normalization or integral assertion is made.

This is an internal adapter of `AdelicSubgroupQuotient`,
`AdelicGroupQuotient`, `SplitUnipotentRationalQuotientCompact`,
`PerfectFieldSplitProof` and `SplitUnipotentAffineTorsorProof`. Its
compactness proof uses only those existing constructions and
Mathlib's compactness of a continuous image; it introduces no new
literature theorem or replacement model of the quotient.
