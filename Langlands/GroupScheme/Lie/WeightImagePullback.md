# Weight witnesses through a subgroup intersection

This internal adapter uses the actual Lie-kernel target maps, the adjoint
weight functoriality in `Lie/Functoriality`, and the compatible intersection
lift in `Lie/Intersection`. It derives no new geometric assertion and uses no
additional literature.

For a homomorphism `s : M ⟶ G` between affine group schemes over a commutative
ring `R`, a commutative group scheme `T`, and `t : T.toGrp ⟶ M`,
`Lie.weightSpaceMap` restricts the actual differential of `s` to each character
weight space. Its underlying vector is `Lie.targetMapLinear s R X`.
It is injective when the underlying scheme map of `s` is monic. The
membership and reflection results are reused from the published
`lieKernelHomLinear_mem_weightSpace` and
`lieKernelHomLinear_mem_weightSpace_iff`; they are not reproved here.

`Lie.weightSpace_lieImage_comp_iff` compares the exact existential
nonzero-vector witnesses for a composite `P ⟶ M ⟶ G` with those for `P ⟶ M`.
The forward direction takes the image in `Lie(M)` of the supplied actual
`P`-kernel point. Its image in `Lie(G)` is the original vector, so reflection
gives its weight condition and nonzeroness follows from the original
nonzero vector. Conversely, the restricted differential preserves the
weight condition, its injectivity preserves nonzeroness, and postcomposition
transports the same `P`-kernel witness.

`Lie.weightSpace_lieImage_subgroupIntersection_iff` applies this comparison to
the second projection of `P ×[G] M`. Its ambient condition requires one fixed
nonzero character-weight vector to have actual Lie-kernel preimages in both
`P` and `M`. The compatible intersection lift supplies an actual kernel point
of the intersection with that same ambient image. The conclusion is precisely
a nonzero vector of the intrinsic weight space for `T ⟶ M` in the Lie-image
of the intersection's second projection. The converse recovers preimages in
both factors using that same vector.

Only `M` and `G` need affineness; `P` is arbitrary. No finite type, smoothness,
field, splitness, maximal-torus, or root hypothesis is imposed. The monomorphism
hypothesis is on the underlying map of schemes over the base. In the rank-one
obstruction application, `P` is an ambient Borel and `M` is a rank-one
centralizer. This adapter supplies the weight-witness comparison only; it does
not establish that a vector belongs to the centralizer Lie-image or that the
intersection is a Borel, nor does it prove the final obstruction.
