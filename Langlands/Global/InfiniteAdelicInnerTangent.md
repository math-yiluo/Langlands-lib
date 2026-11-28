# Tangent conjugation by rational points of `G(F_∞)` and the adjoint action

Module `Langlands.Global.InfiniteAdelicInnerTangent`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`.

Let `F` be a number field, `G` a group scheme over `Spec F` with affine total space and
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, and let `n` be a point of `G` over the base.
Write `g ∈ G(F_∞)` for its image (`G.constantPoint n`).

## Contents

- `groupTangentConjugation_constantPoint`: the tangent map at `1` of conjugation by `g`
  (`groupTangentConjugation`) is the tangent map `pointTangent` of the inner automorphism
  `(G.innerIso n).hom` of `G`.
- `tangentKernel_groupTangentConjugation` (with an affine structure morphism): for every `X` in
  the Lie algebra of `G(F_∞)`, the Lie vector `tangentKernel` of the conjugate of `X` by `g` is
  the image of `tangentKernel X` under the adjoint action `adjoint G F_∞ g` on `lieKernel G F_∞`.

## Proof

The point map of the inner automorphism on `F_∞`-points is conjugation by `g`
(`GroupScheme.comp_innerIso_hom`), so both maps are the derivative at `1` of the same function.
For the second statement, the adjoint action of `g` is the map of Lie algebras induced by the
inner automorphism (`Lie.targetMapLinear_innerIso`), and the naturality of the tangent map
(`tangentPoint_pointTangent`) identifies its value on `tangentKernel X` with the Lie vector of
`pointTangent X`.
