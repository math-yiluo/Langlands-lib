# Actual relative subscheme families

`ImmersionExhaustion.Family` bundles an ambient scheme over a base, its indexed
subschemes as actual slice objects, their immersion morphisms, and inclusions
along an index preorder. The structural triangles over the base are part of
the slice morphisms. The original scheme-level data of the exhaustion statement
give such a family through `Family.ofSchemes`.

`Family.Full` says that one actual inclusion is an isomorphism. The forgetful
functor reflects isomorphisms, so this is equivalent to the underlying
subscheme morphism being an isomorphism. `Family.baseChange` uses the actual
slice pullback functor on all objects, inclusions and transition maps.
Immersions survive this scalar extension by the cartesian base-change square.
Identity and composite scalar changes have equivalent fullness assertions
through the canonical natural isomorphisms of slice pullback functors.

`Family.ArtinianTests` says that the family is full after every local Artinian
affine base change, allowing the index to depend on the test. Composition of
base maps proves stability of this testing condition under any scalar extension.
Finally, the finite-open-cover helper proves fullness from pointwise open
fullness when the index is nonempty and directed and the ambient scheme is
quasi-compact.

This is internal categorical organization for the proof of SGA 3, Exposé IX,
Lemma 6.2, printed pp.53–54 (retained PDF pp.23–24), registered as
`sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The helpers do not prove that Artinian testing alone implies fullness.

The cartesian square on a morphism of slice objects is the transpose of `RelativeIdentityComponent.overPullback_isPullback`.
