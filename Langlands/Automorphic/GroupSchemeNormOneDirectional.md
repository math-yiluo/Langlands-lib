# Directional derivatives on the norm-one adelic group

Let `A : NormOneLieAtlas F G hsmooth e` be an embedded Lie atlas on `G(F∞)¹`, with tangent space
`Fin e → ℝ` at the identity. The module `Langlands.Automorphic.GroupSchemeNormOneDirectional`
defines first-order derivatives of functions on `G(𝔸_F)¹` along the right action of `G(F∞)¹` and
records their calculus. All declarations are in `Langlands.Automorphic.GroupSchemeFunctions`.

## Definition

`normOneDirectional A X f x` is the orbit derivative at the identity, in the direction
`X : Fin e → ℝ`, of the slice `normOneInfiniteSlice F G f x : a ↦ f (x a)` on `G(F∞)¹`. For a
coordinate vector `X = e_l` this is the first-order case of `normOneDifferential A` (the word of
length one).

## Calculus

- `normOneInfiniteSlice_mul`, `normOneDirectional_mul`, `normOneInfiniteSlice_normOneDirectional`:
  slices through right translates are translated slices, and the slice of the derivative is the
  orbit derivative of the slice.
- `normOneDirectional_mul_left`: left translation by `G(𝔸_F)¹` commutes with the derivative.
- `normOneDirectional_eq_sum`: for a differentiable slice, the derivative is linear in the
  direction, `D_X f = ∑_l X_l D_{e_l} f`.
- `normOneDirectional_rational`, `normOneDirectional_level`: left invariance under the rational
  norm-one points and right invariance under a compact finite level pass to the derivative.
- `isNormOneCr_normOneDirectional`: if `f` satisfies `IsNormOneCr A n K₀` and `m + 1 ≤ n ≤ ∞`, the
  derivative in any direction satisfies `IsNormOneCr A m K₀`; the smoothness of the slices is
  `contMDiff_groupDirectionalValue_of_le`.
- `hasDerivAt_normOne_path`: for a path `c` in `G(F∞)¹` differentiable at `t` with translated
  velocity `V`, and a function whose slice at `x` is differentiable at `c t`, the derivative of
  `s ↦ f (x c(s))` at `t` is `D_V f (x c(t))` (`hasDerivAt_comp_path`).
- `tendsto_normOneDirectional`: the derivative is the limit of the difference quotients
  `(k + 1) (f (y χ⁻¹(χ(1) + (k + 1)⁻¹ X)) − f y)` along the chart line of the extended chart `χ` at
  the identity.
- `measurable_normOneDirectional`: for a jointly measurable family `ψ o` with differentiable
  slices, `(o, y) ↦ D_X (ψ o) y` is jointly measurable, as a pointwise limit of the measurable
  difference quotients above.
