# The exact cyclic Lie image of the intrinsic relative root functor

This internal supporting construction identifies the tangent submodule of
the actual all-test relative root functor with the first positive cyclic
weight span. It works over every field in an arbitrary universe. The ambient
group is smooth and affine, the acting torus is split, the homomorphism into
the group is arbitrary, and the character is nonzero. Neither ambient
connectedness, reductivity, maximality nor actual-root occurrence is assumed.

`tangentSubmodule_map` first proves that, under a monomorphic homomorphism of
affine groups, the tangent of the all-test image is the image of the tangent
submodule under the actual derivative. The published
`mem_map_lieKernel_iff` supplies a lift that reduces to the identity:
monicity forces this reduction whenever the image reduces to the identity.

`tangentSubmodule_subgroup` uses the published smooth closed representative
of the actual character-kernel centralizer. Its exact Lie image is the sum of
all integral character multiples. Every cyclic weight therefore lies in the
range of the inclusion's derivative. Equivariance identifies the image of
each source weight space with its ambient weight space intersected with that
range, so the entire cyclic source span maps onto the ambient cyclic span.

The nonzero character is an fpqc quotient onto the multiplicative group.
The published `quotientActionComparison` identifies the root functor with
the image of the identity-limit functor for the descended action on the
centralizer. `dynamicLie`, through the arbitrary-action Lie criterion,
identifies the tangent of this identity-limit functor with its positive
weights. `ActionCharacterWeights` identifies these positive weights with
the cyclic weights of the recovered torus action. Taking the image under
the derivative proves the tangent equality.

`hasLieImage_subgroup` packages the equality using the existing exact
Lie-image predicate. `subgroupTangentEquiv` is the canonical linear
equivalence between the two submodules; its underlying Lie vector is
unchanged.

The provenance is internal: the proof combines the Library's actual kernel
centralizer structure, quotient action comparison, dynamic Lie theorem and
intrinsic action-weight transport. It asserts the exact tangent image of
the intrinsic root functor. It does not identify that functor with a
semigroup subgroup or prove the host `CyclicRootFunctorComparisonStatement`.
