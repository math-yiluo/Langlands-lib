# Sections over open immersions as subrings of the function field

This internal helper module turns opens and open immersions into an integral
scheme `X` into subalgebras of its function field `X.functionField`. It then
checks the chart condition `IsChart` of
`Langlands.CommutativeAlgebra.ChartUniqueFactorization` for sections over affine
opens. It is used in the proof of `SplitSimplyConnectedFactorialStatement` to
view the coordinate rings of the big cell and of its translates as charts of the
coordinate ring of the group.

## Open immersions

For an open immersion `φ : U ⟶ X` with `U` nonempty:

- `toFunctionField φ : Γ(U, ⊤) →+* X.functionField` is the inverse of
  `φ.appIso ⊤` followed by the germ map of the open `φ ''ᵁ ⊤`;
  `toFunctionField_injective` says it is injective.
- `toFunctionField_congr`: equal open immersions give the same map.
- `germToFunctionField_map`: restricting a section does not change its rational
  function.
- `toFunctionField_appTop`: the pull-back of a global function `a` of `X` maps to
  `a` itself, that is, to `algebraMap Γ(X, ⊤) X.functionField a`.
- `toFunctionField_comp`: restricting along a further open immersion
  `a : W ⟶ U` does not change the rational function.
- `toFunctionField_eq_of_comp_eq`: if `ψ ≫ φ = k ≫ φ'` with `k` an open
  immersion and the sections `s`, `s'` agree after pulling back along `ψ` and
  `k`, then `s` and `s'` have the same rational function.

## Opens

For a nonempty open `V` of `X`:

- `sectionSubalgebra V` is the image of `Γ(X, V)` in the function field, as a
  `Γ(X, ⊤)`-subalgebra; `sectionEquiv V : Γ(X, V) ≃+* sectionSubalgebra V`, and
  `algebraMap_sectionSubalgebra` identifies the algebra map with restriction.
- `mem_range_stalk_iff`: for an affine open `W` containing `y`, the rational
  functions coming from the stalk at `y` are exactly the fractions `a / s` of
  sections over `W` with `s` outside the prime of `y`. This uses that the stalk is
  the localization of `Γ(X, W)` at that prime.
- `isFractionRing_top`: for affine `X`, the function field is the fraction field
  of `Γ(X, ⊤)` (from Mathlib's `functionField_isFractionRing_of_isAffineOpen`).
- `comap_primeIdealOf_res`: for affine `X` and an affine open `V ∋ y`, the prime
  of `y` in `Γ(X, V)` contracts to the prime of `y` in `Γ(X, ⊤)`.
- `isChart_sectionSubalgebra`: for affine integral `X` and a nonempty affine
  open `V`, `sectionSubalgebra V` is a chart. A prime `Q` of the subalgebra is
  the prime of a point `y ∈ V`; both localizations in the chart condition are the
  image of the stalk at `y`, described in two ways by `mem_range_stalk_iff`
  (with `W = V` and with `W = ⊤`).
- `exists_prime_comap_eq`: every point `y` of an affine open `V` gives a prime of
  `sectionSubalgebra V` lying over the prime of `y` in `Γ(X, ⊤)`.
- `primeIdealOf_fromSpec_top`: for affine `X`, the point of a prime `q` of
  `Γ(X, ⊤)` has prime ideal `q`.
- `mem_primeIdealOf_of_notMem_basicOpen`: a section over an affine open that is
  not invertible at `y` lies in the prime of `y`.

## Charts from open immersions

- `chartEquiv φ : Γ(U, ⊤) ≃+* sectionSubalgebra (φ ''ᵁ ⊤)`, with underlying
  function `toFunctionField φ` (`chartEquiv_apply_coe`, `toFunctionField_mem`).
- `isAffineOpen_image_top`: the image of an affine scheme under an open
  immersion is an affine open.

The instances `nonempty_top` and `nonempty_image` record that the top open of a
nonempty scheme and the image of a nonempty open are nonempty.

Provenance: internal; standard scheme theory, built on Mathlib's
`Scheme.germToFunctionField` and `IsAffineOpen.isLocalization_stalk`.
