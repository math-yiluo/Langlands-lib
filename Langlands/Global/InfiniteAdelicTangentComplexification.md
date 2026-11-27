# The tangent space of the infinite adelic points

For a number field `F` and an affine group scheme `G` over `F`, smooth of relative dimension `d`,
the module `Langlands.Global.InfiniteAdelicTangentComplexification` identifies the tangent space
at the identity of the real Lie group `G(F ⊗ ℝ)` with the product over the archimedean places `v`
of the dual-number Lie algebras `Lie(G)(F_v)`, and shows that the realizations of the `F`-rational
tangent vectors span it over `ℝ`.

## Dimensions

- `finrank_completion`, `sum_finrank_completion`: `dim_ℝ F_v` is the multiplicity of `v`, and
  these add up to `[F : ℚ]` (`InfinitePlace.sum_mult_eq`).
- `finrank_smoothModel`: the model space has real dimension `d · [F : ℚ]`.
- `finrank_lieKernel_of_smooth`: the dual-number Lie algebra over any field extension `K` of `F`
  has dimension `d` (`Lie.kernelScalarExtension`, `Lie.dimension_eq_of_smoothOfRelativeDimension`).

## The comparison

- `PlaceKernels F G`: the real vector space `∏_v RestrictScalars ℝ F_v (Lie(G)(F_v))`.
- `placeKernelCoordinates`, `placeKernelsEquiv`: `PlaceKernels F G` is linearly equivalent to the
  model space (each factor has dimension `d` over `F_v`).
- `tangentKernelPi`, `tangentKernelPi_injective`, `tangentKernelEquiv`: the joint tangent map of
  `Langlands.Global.InfiniteAdelicPlaceTangentKernel` is injective
  (`eq_zero_of_tangentKernelMap_eq_zero`), hence, comparing it with the equivalence above, a
  linear equivalence `smoothModel F d ≃ₗ[ℝ] PlaceKernels F G`.

## Rational tangent vectors

- `placeKernelVector x`: the images `x_v` of `x ∈ Lie(G)(F)` under `F → F_v`.
- `tangentVector x`: the tangent vector `τ(x)` at the identity whose dual-number points are the
  `x_v`. It is additive (`tangentVector_add`), satisfies `τ(q x) = q τ(x)` for rational `q`
  (`tangentVector_ratCast_smul`), preserves brackets (`tangentVector_lie`, from
  `tangentKernelMap_lie`) and is natural (`tangentVector_naturality`: the derivative of the map
  induced by `f : H → G` sends `τ_H(x)` to `τ_G(df(x))`, from `tangentKernelMap_naturality`).
- `diagonalMap`, `span_range_diagonalMap`: the diagonal image of `F` spans `∏_v F_v` over `ℝ`,
  because it is dense (`InfiniteAdeleRing.denseRange_algebraMap`) and finite-dimensional subspaces
  are closed.
- `scaledKernelVector`, `scaledKernelMap`, `scaledKernelVector_mem_span`: for `a ∈ ∏_v F_v` the
  vector `(a_v x_v)_v` lies in the real span of the `placeKernelVector`s; by linearity in `a` it
  suffices to treat diagonal `a`, where `(f x_v)_v` is the vector of `f x`.
- `single_mem_span_placeKernelVector`, `span_range_placeKernelVector`: every element of a single
  factor `Lie(G)(F_v)` is a sum of vectors `c x_v` with `c ∈ F_v` (scalar extension
  `F_v ⊗_F Lie(G)(F) ≅ Lie(G)(F_v)`), so the `placeKernelVector`s span `PlaceKernels F G`.
- `span_range_tangentVector`: **the realizations `τ(x)` of the rational tangent vectors span the
  tangent space at the identity over `ℝ`.**
