# Identity tangent vectors of `G(F_∞)` correspond bijectively to dual-number kernel points

Module `Langlands.Global.InfiniteAdelicTangentKernelBijective`. The notation is that of
`InfiniteAdelicTangentKernel`: `F` is a number field, `G` an affine group scheme over `F` with
`hsmooth : SmoothOfRelativeDimension d G.X.hom`, `G(F_∞)` carries the Library's manifold
structure `smoothChartedSpace F G hsmooth` modelled on `smoothModel F d = Π_v (Fin d → F_v)`, and
`tangentKernel F hsmooth X ∈ lieKernel G F_∞` is the dual-number point `a ↦ a(1) + ε D_X a` of an
identity tangent vector `X`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointManifold` (general affine schemes):

- `exists_tensor_baseChange_evaluation`: for a `C`-algebra `D` and a regular function `b` of the
  base change `X_D` of an affine `C`-scheme `X`, there is one `t ∈ D ⊗[C] O(X)` with
  `b(p_D) = (p ⊗ id)(t)` for every point `p` of `X` with values in a `D`-algebra `A`. It comes
  from the Library's identification `O(X_D) ≅ D ⊗[C] O(X)` (`ringBaseChangeAffineOverIso`) and
  the naturality of the point–algebra-map correspondence.
- `zeroDeriv_ringPoint_baseChange`: if a family of points `p : M → X(A)` on a manifold `M` has
  zero derivative along a tangent vector `Y` after every original regular function (composed
  with a ring map `c : A → B` to a normed `ℝ`-algebra), then so has every regular function of
  `X_D` at the base-changed points. By the previous theorem it reduces to sums of products of
  constants with original regular functions.

Namespace `Langlands.Global.InfiniteAdelicGroupPoints`:

- `eq_zero_of_zeroDeriv_baseChangeEvaluation`: an identity tangent vector of `G(F_∞)` along
  which every regular function of every base change `G_{F_v}`, evaluated at the `v`-component,
  has zero derivative is zero. The coordinates of the Library's chart at the identity are
  quotients `numerator / denominator` of such regular functions (`RegularChart.apply_eq` for
  `placeRegularChart`), so all chart coordinates have zero derivative, and the chart's
  derivative at its centre is the identity.
- `zeroDeriv_baseChangeEvaluation`: if `D_X a = 0` for all global regular functions `a` of
  `G`, then every regular function of `G_{F_v}` has zero derivative along `X` at the
  `v`-component (by `zeroDeriv_ringPoint_baseChange` with `D = A = F_v`).
- `tangentKernel_injective`: `tangentKernel F hsmooth` is injective. The identity derivation of
  `tangentKernel X` is `D_X` (`kernelDerivationEquiv_tangentKernel`), and `D_{X−Y} = D_X − D_Y`,
  so equal kernel points give `D_{X−Y} = 0`, hence `X = Y` by the two previous theorems.
- `tangentKernel_surjective`: `tangentKernel F hsmooth` is surjective. The Library gives
  `finrank_F (lieKernel G F) = d` (`Lie.dimension_eq_of_smoothOfRelativeDimension`) and
  `F_∞ ⊗[F] lieKernel G F ≅ lieKernel G F_∞` as `F_∞`-modules (`Lie.kernelScalarExtension`), so
  a basis gives an `F_∞`-linear equivalence `e : lieKernel G F_∞ ≅ (Fin d → F_∞)`. By
  `tangentKernel_add` and `tangentKernel_smul`, `X ↦ e(tangentKernel X)` is real-linear into
  `Fin d → Π_v F_v`. It is injective, and source and target both have real dimension
  `Σ_v d · [F_v : ℝ]`, so it is surjective.
- `tangentKernel_bijective`: `Function.Bijective (tangentKernel F hsmooth)`.

## Provenance

Internal: the identification of the Lie algebra of the real Lie group `G(F_∞)` with the
algebraic Lie algebra `Lie(G) ⊗_F F_∞ = ker(G(F_∞[ε]) → G(F_∞))`, the standard description of
tangent vectors of the points of a smooth variety over `ℝ` or `ℂ` as dual-number points.
