# Velocities of curves in a closed subgroup at infinity

Module `Langlands.Global.InfiniteAdelicTangentCurve`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`.

Let `F` be a number field, `G` and `V` group schemes over `Spec F` with affine total spaces,
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, and `j : V ⟶ G` a morphism whose underlying
morphism of schemes is a closed immersion. Let `c : ℝ → G(F_∞)` be a smooth curve, for the
charted space `smoothChartedSpace F G hsmooth`, with `c 0 = 1` and every value `c s` in the image
of `V(F_∞)` under the point map of `j`.

## Contents

- `exists_tangentPoint_curve_eq_comp`: the dual-number point `tangentPoint` of the velocity
  `X = mfderiv c 0 1` at `0` is `y ≫ j` for a point `y` of `V` with values in the dual numbers
  over `F_∞`.
- `tangentKernel_curve_mem_range` (with affine structure morphisms): the Lie vector
  `tangentKernel X` of the velocity lies in the image of `lieKernel V F_∞` under the map
  `Lie.targetMapLinear j` induced by `j`.

## Proof

Let `a` be a regular function on `G` whose pullback to `V` vanishes. Then `a` vanishes on the
image of `V(F_∞)`, so `a ∘ c = 0`. The dual-number point of `X` evaluates `a` to
`a(1) + ε D_X a`, where `D_X a` is the derivative of `a` at `1` in direction `X` at each
archimedean place (`affinePointEvaluation_tangentPoint`, `tangentAlgHom_fst`,
`tangentAlgHom_snd`). Here `a(1) = a(c 0) = 0`, and the chain rule for `placeValue a ∘ c` (a
constant function) gives `D_X a = 0`. So the dual-number point kills the ideal of `V`, and
`exists_comp_eq_of_evaluation_eq_zero` factors it through `j`. For the second statement, the
factor `y` reduces to the identity because its image does (`reduction_tangentPoint`) and `j` is a
monomorphism (`mem_lieKernel_of_comp`), so `y` is a Lie vector of `V` whose image is
`tangentKernel X`.
