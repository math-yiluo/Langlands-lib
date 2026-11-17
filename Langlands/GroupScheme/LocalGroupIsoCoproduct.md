# Local group isomorphism families over scheme coproducts

Let `G,H` be group schemes over any scheme `S`, let `J : Type u` be an
arbitrary index type, and let `V j` be schemes over `S`. For each `j`, suppose
`e j : LocalGroupIso G H (V j)` is a natural isomorphism on every test
scheme equipped with a morphism to `V j`.

`LocalGroupIso.coproduct V e` is a natural group-isomorphism family over
`CoproductChart.sigmaOver V`, the actual coproduct of the schemes `V j`
with its induced structure map to `S`. It requires no scheme representing
isomorphisms, and there is no finiteness, connectedness, nonemptiness,
affineness, flatness, or separation hypothesis on the index, components,
base, or group schemes. The index may be empty or infinite.

`coproduct_refine_ι` says that restriction along each component inclusion
recovers the prescribed family. `coproduct_unique` says that these
restrictions determine the coproduct family uniquely. The more general
`coproduct_toFun_comp` gives the evaluation formula on any commutative
square from a relative test into a component. Thus it also describes
points of the coproduct whose component varies locally on the test.

## Implemented construction

For a morphism `a : T → sigmaOver V`, pull back all the component
inclusions. `CoproductChart.pullbackOpenCover` supplies a Zariski open cover
of `T`. Restrict a `G` point to each member and apply the corresponding
component homomorphism. The values agree on overlaps. For two copies of
the same component this follows from monicity of the component inclusion
and naturality. For distinct components the overlap scheme is empty,
so its two morphisms to `H` agree.

The representable presheaf of `H` is a sheaf on the Zariski slice site by
subcanonicity. Its unique gluing defines
`LocalGroupHom.coproductValue`. Pullback factorization proves the component
evaluation formula after any relative refinement. Testing equality on the
same open cover proves naturality and compatibility with the group law,
producing `LocalGroupHom.coproduct`. Applying the construction to the
component inverse families provides an inverse, since both inverse
identities can be checked on that cover. Finally the component evaluation
formula proves restriction and uniqueness of the isomorphism family.

## Provenance

This is an internal categorical construction for the constant
outer-isomorphism chart proof. It combines the existing all-test
`LocalGroupIso` interface and actual scheme-coproduct cover with Mathlib's
subcanonical Zariski topology. It is not asserted to be a separate theorem
quoted from the reductive-group literature.
