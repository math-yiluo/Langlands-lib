# Fixed subgroups of torus actions

`Langlands.GroupScheme.torusActionFixedSubgroup.{u}` proves the published statement for every field and every supplied closed representative `c : C ⟶ G` of the fixed subgroup of a torus action. It gives smoothness and connectedness of `C`, inheritance of connected reductivity, and the radical comparison over an algebraically closed field on every test scheme. [Statement and conventions](TorusActionFixedSubgroupStatement.md)

## The centralizer in the semidirect product

Write `a` for the action of `S` on `G`. The inclusion `c` intertwines the trivial action of `S` on `C` with `a`. The induced map `C × S ⟶ G ⋊ S` is a closed subgroup inclusion. Conjugation by the acting factor restricts to `a` on the normal factor `G`, so the preimage of its centralizer along `G ⟶ G ⋊ S` is `a.fixedSubgroup`. On each test scheme, a semidirect point is the product of its normal and acting coordinates. The acting coordinate centralizes `S` because `S` is commutative. Membership in the centralizer is therefore equivalent to fixedness of the normal coordinate. This identifies the image of `C × S` with the centralizer functor, including on nonreduced tests.

The group `G ⋊ S` is smooth and affine by the product structure on its underlying scheme, and connected because `G` is connected and `S` is geometrically connected. The torus centralizer in it is smooth and connected by `torusCentralizerSmooth` and `IsTorus.connectedSpace_centralizer`. The first projection of `C × S` has a section given by the identity of `S`. Smoothness follows by affine retraction, and connectedness follows by surjectivity of the projection on the underlying spaces.

## Radical comparison and reductivity

Over an algebraically closed field, the torus is split. For a smooth connected affine normal factor, its radical is normal in the semidirect product by `IsUnipotentRadical.isNormal_comp`. Any smooth connected unipotent normal closed subgroup of the semidirect product projects trivially to the split torus. It factors as a closed normal subgroup of the normal factor and hence lies in that factor's radical. This proves the radical identification for both `G ⋊ S` and `C × S`.

`torusCentralizerUnipotentRadical` now compares those two radicals in `G ⋊ S`. The comparison is pulled back along `G ⟶ G ⋊ S`. This recovers the ranges through the normal factor by monicity and pulls the centralizer back to `a.fixedSubgroup`. The resulting equality is `SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ a.fixedSubgroup` for the supplied radical inclusions `u` and `v`.

For reductivity, base change to `AlgebraicClosure k`. The fixed functor commutes with base change, and `unipotentRadicalExistence` supplies the two radicals over this field. When `G` is connected reductive, the base-changed ambient radical has trivial range. The comparison and monicity of the base-changed `c` then give trivial range for the radical of the base-changed `C`, which yields the geometric radical condition for connected reductivity.

## Source

James S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. See Theorem 13.9 (p. 257), Theorem 17.38 (p. 363), Remark 17.40(a) (p. 364), and Corollaries 17.57–17.59 (p. 371). The semidirect argument retains the acting torus as the second factor of the centralizer. [Torus centralizer radical proof](TorusCentralizerUnipotentRadicalProof.md)
