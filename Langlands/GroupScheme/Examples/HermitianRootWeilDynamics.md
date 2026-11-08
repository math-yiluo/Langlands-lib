# Actual Weil restriction and upper contraction for the weighted Hermitian model

Let `F`, `k` and `L` be fields in an arbitrary common universe, with a finite
extension `k/F` and a separable quadratic extension `L/k`. No separability of
`k/F` or characteristic restriction is imposed. Let `H` be a diagonal Hermitian
middle form on a finite decidable `Middle : Type`, with supplied units
realizing its weights. No middle anisotropy is required here.

The weighted Hermitian scheme over `k` is locally of finite type: its actual
closed inclusion factors its structure morphism through the finite type
Weil-restricted special-linear ambient group. Together with its established
affineness, this permits the existing `AffineWeil.groupScheme` construction.
`WeilSchemeModel.groupScheme` is that actual affine Weil restriction from
`k` to `F`; it is affine and locally of finite type.

For every relative `F`-test scheme `T`, `tensorTest` is the actual spectrum
of `k` tensored with the relative global-section algebra of `T`.
`testPointsEquiv` identifies points of the restricted scheme on `T` with
points of the original weighted scheme on this tensor spectrum.
`tensorForm` is the original middle form extended to the nested tensor
coefficient algebra. Composing with the original all-test matrix equivalence
gives `pointsEquiv`, with target the full determinant-one isometry subgroup
of that weighted form. Both point comparisons satisfy the stated pullback
formulas; coefficient restriction preserves conjugation and every weight.

`upperPoints` transports the original upper points through the inverse
test-point equivalence. Its matrix remains the original weighted upper
matrix. Naturality pulls back every original vector and scalar coordinate;
the ranges therefore define `upperFunctor` on all relative tests.

The ground-field `cocharacter` is the actual transfer of the constructed
diagonal cocharacter by `AffineWeil.cocharacter`. Its point formula evaluates
the original diagonal on the included ground scalar unit. `upperContraction`
transfers the original explicit affine-line contraction by the existing
line-comparison morphism. The general transfer lemmas show that the resulting
curve extends the actual ground-field cocharacter orbit and has identity value
at zero. This proves the all-test inclusion
`upperFunctor_le_dynamicUnipotent`.

This is an internal use of the actual affine Weil restriction and dynamic
transfer interfaces, extending `SU3WeilDynamics` to the weighted Hermitian
scheme. It proves an inclusion, without asserting equality of the upper and
dynamic subgroup functors. Rational generation, parabolic-radical containment,
source smoothness and reductivity, classification and unrestricted local
Kneser–Tits remain separate obligations.
