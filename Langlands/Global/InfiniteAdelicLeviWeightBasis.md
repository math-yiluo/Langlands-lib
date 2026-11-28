# A weight basis of the archimedean Lie algebra adapted to a parabolic: proof

Module `Langlands.Global.InfiniteAdelicLeviWeightBasis`. It proves the statement
`LeviTangentWeightBasisStatement` of `Langlands.Global.InfiniteAdelicLeviWeightBasisStatement`,
using the bijectivity of the archimedean tangent map onto the dual-number Lie algebra
(`tangentKernel_bijective`, module `Langlands.Global.InfiniteAdelicTangentKernelBijective`) and
its naturality `tangentKernel_pointTangent` (module
`Langlands.Global.InfiniteAdelicTangentKernelNaturality`): the Lie vector of `pointTangent j X`
is `Lie.targetMapLinear j F_∞` of the Lie vector of `X`, for a morphism `j : H ⟶ G`.

## Contents

Let `F` be a number field. For a group scheme `G` over `Spec F` and
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, the published module
`Langlands.Global.InfiniteAdelicGroupManifold` provides the charts
`smoothChartedSpace F G hsmooth` of the real manifold `G(F_∞)` and, for these charts, the Lie
group instance `smoothLieGroup F G hsmooth`. The Lie algebra of `G(F_∞)` is its tangent space at
`1` for these charts (Mathlib's `GroupLieAlgebra`, the tangent space at the identity).

In namespace `Langlands.Global.InfiniteAdelicGroupPoints`, for the number field `F`; in every
declaration that involves `G`, `G` is a group scheme over `Spec F` whose total space
`G.X.left` is affine:

- `realAlgebra_finiteDimensional`: `F_∞ = InfiniteAdeleRing F` is finite-dimensional over `ℝ`
  for the real algebra structure `realAlgebra F` of `Langlands.Global.InfiniteAdelicRealTrace`.
- `kernelRealModule F G` and `kernelReal_isScalarTower`: the real structure on
  `lieKernel G F_∞` by restriction of scalars, with the scalar tower `ℝ → F_∞ → lieKernel G F_∞`.
- `tangentKernelLinear F hsmooth`: for a chosen smooth relative dimension
  `hsmooth : SmoothOfRelativeDimension d G.X.hom` of `G`, the tangent map `tangentKernel F hsmooth`
  from the Lie algebra of `G(F_∞)` to `lieKernel G F_∞` as a real-linear map (`tangentKernel_add`,
  `tangentKernel_smul`). With a bijectivity witness `hbij`, `tangentKernelAdeleEquiv F hsmooth hbij`
  is the real-linear equivalence to the dual-number kernel over \(F_\infty\).
  `tangentKernelAdeleEquiv_apply` evaluates it as `Additive.ofMul (tangentKernel F hsmooth X)`.
- `mfderiv_comp_apply_of_eq'`: the chain rule for `mfderiv` at a point given up to an equation.
- `mem_span_curveTangents_iff`: for `G` with affine total space and a smooth relative dimension
  `hsmooth` as above, and a closed subgroup `j : V ⟶ G` (a closed immersion on total spaces),
  where `V` is a group scheme over `Spec F` with affine total space `V.X.left` and a chosen
  smooth relative dimension `hsmoothV : SmoothOfRelativeDimension e V.X.hom`, a tangent vector
  `X` of `G(F_∞)` at `1` lies in the real span of
  `curveTangents F hsmooth (Set.range (V.affinePointsTarget j F_∞))` if and only if
  `Additive.ofMul (tangentKernel F hsmooth X)` lies in the range of
  `Lie.targetMapLinear j F_∞`.
- `units_map_two_zpow`: the `m`-th power of the unit `2` of `F` in `F_∞` is the real scalar
  `2 ^ m`.

In namespace `Langlands.Global`:

- `mem_span_smulTower_map`: if `x` is an `S`-combination of a family `e` of vectors indexed by
  `i` with `P i`, and `bS` is an `R`-basis of `S`, then the image of `x` under an `R`-linear
  equivalence `f` is an `R`-combination of the vectors `f (bS k • e i)` with `P i`
  (`Module.Basis.smulTower`).
- `leviTangentWeightBasis`: the proof of `LeviTangentWeightBasisStatement`.

## Proof of `mem_span_curveTangents_iff`

If `X` is in the span, its Lie vector is in the range: the real-linear map
`tangentKernelLinear` sends every curve tangent into the range of `Lie.targetMapLinear j F_∞`
(`tangentKernel_curve_mem_range`), and that range is an `F_∞`-submodule, hence a real
submodule. Conversely, if the Lie vector of `X` is `Lie.targetMapLinear j F_∞ y`, surjectivity
of the tangent map of `V` gives a tangent vector `Y` of `V(F_∞)` with Lie vector `y`. The Library
lemma `exists_contMDiff_curve_fixed` (for the identity involution) gives a smooth curve `c_V` in
`V(F_∞)` through `1` with velocity `Y`. Its image `c` in `G(F_∞)` is smooth
(`contMDiff_affinePointsTarget`) and stays in the image of `V(F_∞)`. By the chain rule and
`tangentKernel_pointTangent`, the Lie vector of its velocity is that of `X`, so the velocity is
`X` by injectivity of the tangent map of `G`. Hence `X` is itself a curve tangent.

## Proof of `leviTangentWeightBasis`

The total space of `V` is affine because `V` is a closed subgroup of the affine `Q`
(`BorelFieldExtension.isAffineHom_source`). `V` is smooth and connected, so it is smooth of some
relative dimension (`smoothConnectedRelativeDimension`).
`exists_leviCocharacterLieWeightBasis_baseChange` over `A = F_∞` gives a central cocharacter `ψ`
of `M'`, an `F_∞`-basis `e` of `lieKernel G F_∞` indexed by `Fin n` and integer weights `w` with
the eigenvector and spanning properties for `lieKernel M' F_∞` and `lieKernel V F_∞`.

The real basis is `b`, the tower basis `bA.smulTower e` (with `bA = Module.finBasis ℝ F_∞`)
transported to the Lie algebra of `G(F_∞)` by the inverse of `B = tangentKernelAdeleEquiv` and reindexed
by `Fin`. Each index `a` corresponds to a pair `(k, i)` of an index `k` of `bA` and an index `i` of
`e`, with `B (b a) = bA k • e i`; here `bA k` is an element of `F_∞`, in general not a real number.
The weight of `b a` is `w i`. By `mem_span_smulTower_map`, for a predicate `P` on weights, a Lie
vector `X` with `B X` in the `F_∞`-span of the `e i` with `P (w i)` lies in the real span of the
`b a` whose weight satisfies `P`. The point is `t = ψ(2)`, the image in `M'(F_∞)` of the base point
of `𝔾_m` given by the unit `2 ∈ F` (`gmBasePoint`). Its image in `G(F_∞)` is the base point of
`ψ ≫ l' ≫ q` at `2`.

1. Eigenvectors: `tangentKernel_groupTangentConjugation` turns tangent conjugation by the base
   point `ψ(2)` into the adjoint action on `lieKernel G F_∞`. On `e i` this action is
   multiplication by `2 ^ (w i)` (`characterValue_powerHom_constantPoint_gmBasePoint`,
   `units_map_two_zpow`). The adjoint action is `F_∞`-linear, so it also multiplies
   `B (b a) = bA k • e i` by `2 ^ (w i)`. Since `B` is injective and real-linear, tangent
   conjugation by `ψ(2)` multiplies `b a` by the real number `2 ^ (w i)`.
2. Injectivity: by `tangentKernel_pointTangent`, `B ∘ dι` is
   `Lie.targetMapLinear (l' ≫ q)` composed with the tangent map of `M'`. The latter is bijective
   (`tangentKernel_bijective`), and the former is injective because `l' ≫ q` is a monomorphism
   (`Lie.targetMapLinear_injective`).
3. and 4. Weight zero: if `b a` has weight zero, its image under `B` is `bA k • e i`, where
   `k` and `i` are the corresponding tower indices and `w i = 0`. The vector `e i` lies in the
   image of `lieKernel M' F_∞` under `Lie.targetMapLinear (l' ≫ q) F_∞`. That image is an
   `F_∞`-submodule, so it contains `bA k • e i`. Surjectivity of the tangent map of `M'` and
   `tangentKernel_pointTangent` give a tangent vector of `M'(F_∞)` mapping to `b a`. Conversely,
   for a tangent vector `Y` of `M'(F_∞)`, `B (dι Y)` lies in that image, hence in the
   `F_∞`-span of the weight-zero `e i`, and `mem_span_smulTower_map` puts `dι Y` in the real span
   of the weight-zero `b a`.
5. Positive weights: if `b a` has positive weight, `B (b a) = bA k • e i` with `w i > 0`. The vector
   `e i` lies in the image of `lieKernel V F_∞` under `Lie.targetMapLinear (iV ≫ q) F_∞`, an
   `F_∞`-submodule, so `bA k • e i` lies there too. By surjectivity of the tangent map of `V` and
   `tangentKernel_pointTangent`, `b a = dι_V Y` for a tangent vector `Y` of `V(F_∞)`. The Library
   lemma `exists_contMDiff_curve_fixed` (for the identity involution) gives a smooth curve `c_V` in
   `V(F_∞)` through `1` with velocity `Y`. Its image in `G(F_∞)` is smooth
   (`contMDiff_affinePointsTarget`), lies in `S_V`, and has velocity `dι_V Y = b a` by the chain
   rule.
6. Curve tangents: `tangentKernel_curve_mem_range` places the Lie vector of the velocity of a
   smooth curve in `S_V` through `1` in the image of `lieKernel V F_∞`. That image lies in the
   `F_∞`-span of the positive-weight `e i`, and `mem_span_smulTower_map` puts the velocity in the
   real span of the positive-weight `b a`.

Bijectivity of the tangent map (`tangentKernel_bijective`) is used for `G`, `M'` and `V`.
