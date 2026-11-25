# Finiteness of right translates under sums, products and polynomials

Lean module: `Langlands.Representation.Archimedean.TranslateFinite`.

This module provides closure properties of finite-dimensional spans of right translates, for
functions on a group `G`. It applies them to show that polynomial functions of the matrix entries
on `O(n)` are `O(n)`-finite (`finiteDimensional_span_eval`). This is used to produce
`O(n)`-finite vectors (annihilators, sign vectors) through the extension lemma of
`PrincipalSeriesExtension`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.TranslateFinite`.

## Definitions

`IsTranslateFinite s f`, for a family `s : ι → G`, means that the right translates
`Whittaker.rightTranslation ℂ G (s i) f = f(· s_i)` span a finite-dimensional complex
subspace. With `s` the inclusion of a subgroup `K`, this is exactly the condition in
`mem_kFiniteVectors_iff`. With `s = id` on `O(n)`, it is the finiteness hypothesis of the
extension lemma.

## Results

* `isTranslateFinite_const`: constant functions.
* `isTranslateFinite_add`: the translates of `f + g` lie in the sum of the two spans.
* `isTranslateFinite_mul`: the translates of `f g` lie in the product of the two spans, in the
  algebra of functions `G → ℂ`. That product is finitely generated (`Submodule.FG.mul`).
* `isTranslateFinite_pow` and `isTranslateFinite_smul` follow.
* `isTranslateFinite_entry`: on `O(n)`, the right translates of a matrix entry `κ ↦ κ_{ij}` lie
  in the span of the entries `κ ↦ κ_{il}`, since `(κ k)_{ij} = ∑_l κ_{il} k_{lj}`.
* `finiteDimensional_span_eval`: for every `P ∈ ℂ[X_{ij}]`, the function
  `κ ↦ P(κ_{ij})` on `O(n)` is `O(n)`-finite. The proof is by `MvPolynomial.induction_on`, using
  the constant, sum, product and entry cases.

Provenance. Derived, internal infrastructure (elementary linear algebra).
