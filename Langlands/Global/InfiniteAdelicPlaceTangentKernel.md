# Tangent vectors of the infinite adelic points as dual-number points

Let `F` be a number field and `G` an affine group scheme over `F`, smooth of relative dimension
`d`, with the Library's real Lie group structure on `G(F ⊗ ℝ)` (`InfiniteAdelicGroupPoints F G`,
charts `smoothChartedSpace F G hsmooth`, model space `smoothModel F d`). The module
`Langlands.Global.InfiniteAdelicPlaceTangentKernel` attaches to each tangent vector `X` at the
identity and each archimedean place `v` a dual-number point of `G` over the completion `F_v`, and
proves that this construction is injective (jointly over all `v`), preserves brackets and is
natural in `G`.

## Construction

- `kernelEvaluation`, `kernelEvaluation_injective`: a point of the identity kernel
  `lieKernel G K` (a `K[ε]`-point reducing to the identity) is determined by the `ε`-parts of
  the values of the global regular functions of `G` at it.
- `mdiffSubalgebra`, `manifoldJet`: the algebra of real functions on a manifold that are
  differentiable at a point `x₀`, and its first-order jet `h ↦ h(x₀) + (dh_{x₀} X) ε` with values
  in the dual numbers.
- `isRegularFamily_atPlace`, `placePointValue`: the values of a regular function at the `F_v`-component
  of a point of `G(F ⊗ ℝ)` are differentiable at the identity.
- `tangentKernelPoint`, `tangentKernelMap`: composing the jet in the direction `X` with the
  regular family `g ↦ g_v` gives an `F_v[ε]`-point of `G` in the identity kernel; this defines a
  real-linear map `tangentKernelMap F G hsmooth v` from `smoothModel F d` to
  `RestrictScalars ℝ F_v (Additive (lieKernel G F_v))`.
- `kernelEvaluation_tangentKernelMap`: the `ε`-part of the value of a regular function `a` at this
  point is the derivative at the identity of `g ↦ a(g_v)` in the direction `X`.

## Main results

- `eq_zero_of_tangentKernelMap_eq_zero`: **if the dual-number points of `X` at all archimedean
  places are trivial, then `X = 0`.** Choose a closed embedding `ρ : G → GL_N`
  (`affineLinearEmbeddingStatement`); its base changes to the completions are closed
  (`isClosedSubgroup_baseChange`) and their matrix coefficients are values of global regular
  functions (`exists_affineMatrix_entry_eq`, `realizationMatrix_baseChange`). The hypothesis says
  all these coefficients have zero derivative in the direction `X`, and the Library's
  `eq_zero_of_zeroDeriv_realization` concludes.
- `tangentKernelMap_lie`: **the dual-number point of the Lie bracket `⁅X, Y⁆` of the Lie group is
  the bracket of the dual-number points**, for the scoped brackets of
  `Langlands.GroupScheme.Lie.FieldAlgebraLie`. With `ρ` as above, the tangent matrix of the
  dual-number point is the differential of the smooth matrix-valued map `g ↦ ρ(g_v)`
  (`kernelDifferential_tangentKernelMap`); the Library's `matrixDifferential_lie` computes the
  differential of a bracket as a commutator, `MatrixRepresentation.kernelDifferential_commutator`
  does the same on the algebraic side, and `Lie.kernelDifferential_injective` concludes.
- `tangentKernelMap_naturality`: **for a homomorphism `f : H → G`, the dual-number point of the
  derivative at the identity of `H(F ⊗ ℝ) → G(F ⊗ ℝ)` applied to `X` is the image under the
  tangent map of `f` of the dual-number point of `X`.** Both sides are compared through
  `kernelEvaluation`: the chain rule for `g ↦ a(f(g)_v)` (`placeValue_affinePointsTarget`, and
  the smoothness of the point map, the Library's `contMDiff_affinePointsTarget` from
  `Langlands.Global.InfiniteAdelicLeviEnveloping`) against `affinePointEvaluation_postcomp`.

## Sources

The identification of the Lie algebra of the real points of a group scheme with its algebraic
Lie algebra over `ℝ` via dual numbers is classical (A. Borel, *Linear Algebraic Groups*, 2nd ed.,
§I.3; J.-P. Serre, *Lie Algebras and Lie Groups*, Part II); the proofs here are direct.
