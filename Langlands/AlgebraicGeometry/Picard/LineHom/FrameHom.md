# Morphisms between module sheaves with frames on a common cover

Helper module for the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement`.

Setting: a scheme `X`, an open cover `T : ι → X.Opens` with `⨆ i, T i = ⊤`,
sheaves of modules `M` and `N` with frames `e i` of `M` and `f i` of `N` on
`T i` (`Scheme.Modules.IsFrameOn`), and unit transition functions `g` and `h`
with `IsTransition e g` and `IsTransition f h` (the Library notions of
`Picard/CocycleLineBundleFrame`).

- `IsCocycle.self_eq_one`: a unit cocycle is `1` on the diagonal `T i ⊓ T i`.
- `IsCocycle.mul_swap_eq_one`: `g i j` times the restriction of `g j i` to
  `T i ⊓ T j` is `1`.
- `isGaugeFamily_iff_of_lt`: for cocycles `g`, `h` on a linearly ordered index
  type, a family `a i ∈ Γ(X, T i)` satisfies the Library relation
  `IsGaugeFamily g h a` (namely `a i|·g i j = h i j·a j|` on every
  `T i ⊓ T j`) as soon as this holds for the pairs `i < j`.
- `frameHomEquiv`: the bijection between `M ⟶ N` and the families `a` with
  `IsGaugeFamily g h a`.
- `frameHomEquiv_spec`: the family `a` of `φ` satisfies
  `φ (e i) = a i • f i`; `frameHomEquiv_apply_eq` says this relation
  determines `a`.

Proofs as implemented. The diagonal identity comes from the restricted
cocycle relation `cocycle_res` at `(i, i, i)` by cancelling the unit `g i i`;
the swap identity from `cocycle_res` at `(i, j, i)` and the diagonal identity.
For `isGaugeFamily_iff_of_lt` the case `i = j` uses the diagonal identity and
the case `j < i` restricts the relation for `(j, i)` to `T i ⊓ T j` and
combines it with the two swap identities (`linear_combination`).
`frameHomEquiv` transports along the Library isomorphisms
`frameIso : M ≅ glued g` and `frameIso : N ≅ glued h` and uses the Library
classification of morphisms `glued g ⟶ glued h` by gauge families
(`coeff`, `gaugeHom`, `eq_gaugeHom`, `coeff_gaugeHom` in
`Picard/CocycleLineBundleGauge`). `frameHomEquiv_spec` evaluates the
transported morphism on the generating section `genSec` (`app_genSec_top`),
which `frameIso.inv` sends to the frame (`frameIso_inv_app_genSec`).
`frameHomEquiv_apply_eq` uses that `f i` is a frame, so coefficients against
it are unique.

This is the standard description of morphisms between line bundles given by
transition functions on a trivializing cover; it is internal to this proof.
