# Tori centralizing Lie elements in characteristic zero

This module proves `CharZeroTorusLieCentralizerStatement.{u}` (stated in
`Lie/TorusLieCentralizerStatements`) as the theorem
`Langlands.GroupScheme.charZeroTorusLieCentralizer`. Let `k` be a field of
characteristic zero, `G` a smooth affine group scheme over `Spec k`,
`j : T ⟶ G` a homomorphism from a torus, and `Y` a Lie element of `G`. If
every tangent vector of `T` maps into the Lie centralizer
`Lie.elementCentralizerLie G Y`, then
`SubgroupFunctor.range j ≤ Lie.elementCentralizer G Y`.

## Proof

The proof follows the closed-subgroup route given in the statement's
Markdown. It uses no weight decomposition.

1. *Geometry of the torus.* `IsTorus.smooth` and `IsTorus.connectedSpace`
   (`Torus/Geometry`) make `T` smooth with connected underlying space.
   `SplittingAssembly.isAffine_of_isTorus` makes its underlying scheme
   affine.
2. *Closed representative of the centralizer.*
   `Lie.elementCentralizer_isClosedRepresentable G Y` gives a group scheme
   `C` and a closed immersion `i : C ⟶ G` that represents
   `Lie.elementCentralizer G Y`. Since `G` is affine over `k`, so is `C`.
3. *Its preimage in `T`.* Let `T'` be `SubgroupPreimage.groupScheme j i`,
   the pullback of `i` along `j`, with inclusion
   `SubgroupPreimage.inclusion j i : T' ⟶ T`. This inclusion is a closed
   subgroup (`SubgroupPreimage.isClosedSubgroup`), and `T'` is affine
   (`SubgroupPreimage.isAffineHom`). `T'` is locally of finite type over `k`
   because its structure map factors through the closed immersion into `T`.
   Cartier's theorem (`affineCartierSmooth`) then makes `T'` smooth, since
   `k` has characteristic zero.
4. *Surjectivity on tangent spaces.* Let `t` be a tangent vector of `T`.
   By hypothesis its image under `j` lies in
   `Lie.elementCentralizerLie G Y`. By `SubgroupFunctor.lie_eq_range` this
   submodule is the range of the tangent map of `i`, so the image is the
   image of some tangent vector `c` of `C`. The universal property of the
   intersection Lie kernel (`Lie.kernelIntersectionLift`, `Lie/Intersection`)
   combines `t` and `c` into a tangent vector of `T'`. That vector maps to
   `t` (`Lie.kernelIntersectionLift_fst`). So the tangent map of
   `T' ⟶ T` is surjective.
5. *The preimage is everything.* `T` is smooth, affine and connected, `T'` is
   smooth and affine, and `T' ⟶ T` is a closed subgroup with surjective
   tangent map. `Lie.isIso_of_surjective_targetMapLinear`
   (`Lie/DimensionInduction`) then makes the inclusion an isomorphism.
6. *Conclusion.* Rewrite the centralizer as the range of `i`. A point
   `t ≫ j` of the range of `j` is the point
   `t ≫ inv (inclusion) ≫ projection` of the range of `i`. This uses the
   commutativity of the pullback square (`SubgroupPreimage.isPullback`).

## Provenance

This is an internal deduction from Library results. The statement is
derived and internal; see `Lie/TorusLieCentralizerStatements.md`. The
argument is the standard characteristic-zero argument: by Cartier's
theorem a closed subgroup is smooth, and a smooth closed subgroup of a
connected smooth group with full tangent space is the whole group. This
module claims nothing beyond the statement above.
