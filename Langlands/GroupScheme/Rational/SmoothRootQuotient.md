# Smooth maps on intrinsic relative root groups

This internal construction restricts an actual group-scheme homomorphism
`q : G ⟶ H` to supplied representatives of the intrinsic root functors
`RelativeRoot.subgroup i a` and `RelativeRoot.subgroup (i ≫ q) a`.
The construction `rootMap` works over any base and for any character.
Its composite with the target root inclusion is the source root inclusion
followed by `q`, by `rootMap_comp`.

Over an arbitrary field and universe, assume the two ambient groups are
smooth and affine, the acting torus is split, the character is nonzero,
and `q` is smooth. The differential maps the source root tangent submodule
onto the target one. The proof rewrites both tangent submodules as the
positive cyclic character spans using `RootSubgroupLieImage`, and applies
the smooth equivariant span surjectivity theorem in `SmoothTangentWeights`.
Conjugation is equivariant under every group-scheme homomorphism.

For affine representatives, this implies that the differential of `rootMap`
is surjective: identify each root tangent submodule with the range of its
representing inclusion, lift a target vector through the image equality,
and cancel the injective differential of the target inclusion. Smoothness
of the representatives follows from `RootSubgroupRepresentability`;
that module and the proved `dynamicConnected` give connectedness of the
target representative. The proved criterion
`Lie.smoothSurjectiveOfSurjectiveDifferential` then makes this same
restricted homomorphism smooth and surjective on scheme points.

If the field is algebraically closed, every rational point of the target
representative has a rational lift through this homomorphism, by
`Lie.exists_rational_lift_of_mem_range`.
The theorem `exists_root_point_lift_of_smooth` removes the supplied
representatives from this conclusion: choose the smooth closed representatives
provided by `RootSubgroupRepresentability`, derive their affineness from the
closed inclusions, and lift the represented target point. The commuting square
then gives a lift through the original map `q` which belongs to the source
intrinsic root functor.

This is a derived construction from the named published interfaces, with
no separate original-literature claim. It does not require reductivity,
maximality or injectivity of the torus map, ambient connectedness, or
surjectivity of the ambient map. It establishes no splitness or connectedness
of its kernel and no facet root-survival or coroot comparison.
