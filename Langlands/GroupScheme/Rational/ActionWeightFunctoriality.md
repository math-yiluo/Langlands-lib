# Equivariant functoriality of intrinsic action weights

This internal supporting module treats an actual equivariant homomorphism
f from an affine group G to an affine group K over an arbitrary field k.
The two supplied actions a and b have the same commutative acting group S.
Equivariance is the published all-test `AutomorphicAction.IsEquivariant`
condition. No torus, smoothness, connectedness, or representability assumption
is added.

`map_mem_actionEigenvectors` proves that the actual derivative
`Lie.targetMapLinear f k` preserves the intrinsic eigenvector condition
after every coefficient extension and against every S-point. Compatibility
of the derivative with coefficient change and epsilon scaling reduces the
target equation to postcomposition of the source equation, using equivariance.
`mem_actionEigenvectors_target_iff` reflects the same condition when the
underlying map over the base is a monomorphism, by cancelling that map.

The published `mem_actionWeightSpace_iff` identifies each intrinsic weight
space with its eigenvectors. It therefore gives `map_mem_actionWeightSpace`
and, under a monomorphism, `mem_actionWeightSpace_target_iff`.
`actionWeightSpaceMap` bundles the derivative restricted to the source and target
weight spaces as a linear map, with its explicit evaluation formula and
injectivity under a monomorphism.
`actionWeightSpace_eq_comap` packages reflection as an inverse-image equality;
`map_actionWeightSpace_eq_inf_range` identifies the image weight space with
the intersection of the target weight space and the actual derivative range.

For any subgroup functor F of G, `actionWeightSupport_map_eq` proves that the
support of its actual pointwise image under an equivariant monomorphism is
exactly its source support. In the forward construction from a source witness,
the injective derivative preserves its nonzero value and its weight, while
pointwise image membership gives the required target membership. Conversely,
a target support witness lifts through pointwise image membership. Reduction
to the identity commutes with the homomorphism, and monomorphism cancellation
forces the lifted point to belong to the source identity kernel. Weight
reflection and the equality with the target vector then give a nonzero source
witness. F need not be smooth, represented, or invariant.

The provenance is internal: the implementation uses actual dual-number target
maps from `Lie.KernelTargetMaps`, the published intrinsic eigenspace criterion,
and the existing pointwise image of subgroup functors. It asserts no geometric
existence or cyclic-tail comparison.

The restricted linear map reuses `RelativeRoot.actionWeightSpaceMap` from
`TangentWeightTransport`. Reflection, injectivity and support transport reuse
the published `ActionWeightTransport` and `TangentWeightTransport` results,
with the explicit all-test equivariance arguments supplied by `hf`.
`tangentSubmodule_range` identifies the tangent-image formulation with the
derivative-range formulation. Preservation without a monomorphism is retained.
