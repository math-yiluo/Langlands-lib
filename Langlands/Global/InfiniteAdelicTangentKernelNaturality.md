# Naturality of the dual-number tangent points of `G(F_∞)`

Module `Langlands.Global.InfiniteAdelicTangentKernelNaturality`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The notation is that of
`InfiniteAdelicTangentKernel`. For a morphism of group schemes `j : H ⟶ G` between affine group
schemes with smooth structures, `pointTangent F hsmoothH hsmooth j` (module
`InfiniteAdelicLeviEnveloping`) is the tangent map at the identity of `j : H(F_∞) → G(F_∞)`.

## Declarations

- `mfderiv_comp_apply_of_eq`: the chain rule for maps between manifolds modelled on real normed
  spaces, with the intermediate point given up to an equality `f x = y`.
- `regularDerivative_pointTangent`: `D_{dj(X)} a = D_X (a ∘ j)` for every global regular
  function `a` of `G`. This is the chain rule, with the smoothness of `j` on archimedean points
  (`contMDiff_affinePointsTarget`) and `j(1) = 1`.
- `tangentPoint_pointTangent`: `tangentPoint (dj(X)) = j(tangentPoint X)` as points of `G` over
  `F_∞[ε]`. Both points have the same regular-function values: the constant parts agree because
  `j(1) = 1`, and the `ε`-parts by the previous theorem.
- `tangentKernel_pointTangent`: the same statement for the kernel elements,
  `tangentKernel (dj(X)) = Lie j (tangentKernel X)` in `Additive (lieKernel G F_∞)`, where
  `Lie j = Lie.targetMapLinear j F_∞`.

## Provenance

Internal: functoriality of the description of tangent vectors as dual-number points.
