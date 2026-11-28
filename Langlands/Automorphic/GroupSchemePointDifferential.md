# Differentials of homomorphisms on actual infinite adelic points

Module `Langlands.Automorphic.GroupSchemePointDifferential`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`.

Fix a number field `F` and affine group schemes `G`, `H` over `F` with atlases
`hG : SmoothOfRelativeDimension d G.X.hom` and `hH : SmoothOfRelativeDimension e H.X.hom`.
The infinite adelic points carry the Library's charts `smoothChartedSpace` and Lie group
structures `smoothLieGroup`. A homomorphism `f : H ⟶ G` acts on points by
`H.affinePointsTarget f`, that is `x ↦ x ≫ f.hom.hom`.

## The complexified Lie differential

- `complexPointLieDifferential hH hG f` is the complex-linear extension
  (`Langlands.Algebra.ComplexLieExtension.extendLieHom`) of the real Lie algebra map
  `pointTangentLieHom F hH hG f` of module `Langlands.Global.InfiniteAdelicLeviEnveloping`,
  the derivative at `1` of the point map. That module proves that the point map is smooth
  (`contMDiff_affinePointsTarget`) and that its derivative preserves Mathlib's bracket.
  The enveloping map `UniversalEnvelopingAlgebra.lift ℂ (ι ∘ complexPointLieDifferential)`
  is the same map as `pointEnvelopingMap` of that module.
- `complexPointLieDifferential_apply` identifies its values with those of
  `complexPointDifferential` (module `Langlands.Automorphic.GroupSchemeParabolicTangentStatement`).
  Both use the same base change of `mfderiv` at `1`, so the identification holds by definition.

## Pullback of smooth functions

- `Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback f` is the complex-linear map `u ↦ u ∘ (H.affinePointsTarget f)` from the
  plot-smooth functions on `G(F_∞)` to those on `H(F_∞)`. Plot smoothness is preserved by
  `GroupScheme.IsPlotSmooth.postcomp`.
- `pointPullback_plotSmoothDifferential` shows that pullback carries the derivative
  `plotSmoothDifferential` in the direction `dφ X` to the derivative in the direction `X`.
  Here `φ` is the point map. This follows from the chain rule
  `groupDirectionalValue_comp_hom` of module `Langlands.Geometry.Manifold.SmoothGroupHomLie`,
  with `isPlotSmooth_iff_contMDiff` for smoothness and `contMDiff_affinePointsTarget`.
- `pointPullback_envelopingAction` shows that for every element `w` of the enveloping algebra of
  `H(F_∞)`, pullback intertwines `plotSmoothEnvelopingAction` of the image of `w` under the
  enveloping map of `complexPointLieDifferential` with the action of `w`. The proof lifts `w`
  to the tensor algebra and inducts over scalars, generators, products and sums. On pure
  tensors `z ⊗ X` of generators the previous item applies after
  `complexPlotSmoothLieAction_tmul`.

These constructions follow from the chain rule and from the universal property of the
enveloping algebra. The equivariance theorem takes the
`AdelicDifferentialCommutator` hypotheses for the two enveloping actions.
