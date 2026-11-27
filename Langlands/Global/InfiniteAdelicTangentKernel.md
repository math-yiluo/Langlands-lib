# Identity tangent vectors of `G(F_∞)` as dual-number points

Module `Langlands.Global.InfiniteAdelicTangentKernel`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`.

Let `F` be a number field, `G` an affine group scheme over `F`, and
`hsmooth : SmoothOfRelativeDimension d G.X.hom`. Equip `G(F_∞)` with the Library's real
manifold structure `smoothChartedSpace F G hsmooth` and the pinned `RCLike` structures on the
archimedean completions. A tangent vector `X` at the identity (an element of
`GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`) is turned into a
point of `G` over the dual numbers `F_∞[ε]` that reduces to the identity, that is, an element
of the dual-number Lie kernel `lieKernel G F_∞`.

## Declarations

- `placeValue F v a x`: the value at the infinite place `v` of the global regular function
  `a` (an element of `AffineCoordinateRing F G.X`) at `x ∈ G(F_∞)`. `placeValue_add`,
  `placeValue_mul` and `placeValue_algebraMap` record that `a ↦ placeValue F v a` is additive,
  multiplicative and constant on scalars. `contMDiff_placeValue` is its smoothness, from the
  published `contMDiff_completionEvaluation`.
- `identityValue F a ∈ F_∞`: the value of `a` at the identity.
- `regularDerivative F hsmooth X a ∈ F_∞`: at each place `v`, the real derivative at the
  identity along `X` of `placeValue F v a` (an element of the completion `F_v`).
- `regularDerivative_add`, `regularDerivative_mul` (Leibniz rule
  `D_X(ab) = a(1) D_X b + b(1) D_X a`), `regularDerivative_algebraMap` (constants have
  derivative `0`), `regularDerivative_one`, `regularDerivative_zero`. The proofs use Mathlib's
  sum and product rules for manifold derivatives into the normed algebras `F_v`.
- `tangentAlgHom F hsmooth X : AffineCoordinateRing F G.X →ₐ[F] F_∞[ε]`,
  `a ↦ a(1) + ε D_X a`. The laws above make it an `F`-algebra map. `tangentAlgHom_fst` and
  `tangentAlgHom_snd` give its two components.
- `tangentPoint F hsmooth X`: the point of `G` over `F_∞[ε]` corresponding to `tangentAlgHom`
  under the published `affineSchemePointEquiv`. `affinePointEvaluation_tangentPoint` evaluates
  regular functions at it. `reduction_tangentPoint` says that it reduces to the identity:
  both points have the same regular-function values, and points of affine schemes are
  determined by these values.
- `tangentKernel F hsmooth X : lieKernel G F_∞`, the resulting kernel element.
- `affinePointEvaluation_tangentPoint_snd`: the `ε`-part of the value of `a` at
  `tangentPoint X` is `D_X a`.
- `regularDerivative_comp`: for a morphism of group schemes `j : G ⟶ H` and a regular function
  `b` of `H`, `D_X (b ∘ j)` is the `ε`-part of the value of `b` at the image of
  `tangentPoint X` in `H(F_∞[ε])`.

- `affinePointEvaluation_lieKernel`: an element `x` of `lieKernel G F_∞` evaluates a regular
  function `a` to `a(1) + ε · ∂_x(a)`, where `∂_x` is the identity derivation
  `Lie.kernelDerivationEquiv G x` applied to the image of `a` under
  `LocalModularCharacter.coordinateComparison` (from `affinePointEvaluation_eq_pointCoordinates`
  and `Lie.pointCoordinates_kernel`).
- `kernelDerivationEquiv_tangentKernel`: the identity derivation of `tangentKernel X` is `D_X`.
- `regularDerivative_add_left`: `D_{X+Y} = D_X + D_Y`, by linearity of the manifold derivative
  in the tangent vector.
- `affinePointEvaluation_tangentKernel_add` and `tangentKernel_add`:
  `tangentKernel (X + Y) = tangentKernel X * tangentKernel Y`. Both points have the same
  regular-function values, because the identity derivation of a product in the kernel is the
  sum of the identity derivations (`Lie.kernelDerivationEquiv_mul`).

- `realAdele F r`: the diagonal image of `r ∈ ℝ` in `F_∞`.
- `regularDerivative_smul_left`, `affinePointEvaluation_tangentKernel_smul` and
  `tangentKernel_smul`: `tangentKernel (r • X)` is the `ε`-scaling (`lieKernelScale`) of
  `tangentKernel X` by `realAdele F r`. The identity derivation of an `ε`-scaled kernel point is
  the scaled derivation (`Lie.kernelDerivationEquiv_scale`).

## Provenance

Internal. This is the standard description of tangent vectors at the identity as dual-number
points (derivations at the identity), applied to the Library's archimedean manifold structure.
This module does not prove that `X ↦ tangentKernel X` is bijective or compatible with Lie
brackets; the modules `InfiniteAdelicTangentKernelBijective` (`tangentKernel_bijective`) and
`InfiniteAdelicTangentKernelBracket` (`tangentKernel_lie`) do.
