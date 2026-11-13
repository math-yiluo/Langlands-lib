# Local anisotropic simply connected type A is inner, given the Hermitian model

This module proves that the published proposition
`Langlands.GroupScheme.LocalAnisotropicTypeAInnerStatement` follows from
`Langlands.GroupScheme.LocalOuterTypeAHermitianModelStatement` (stated in
`Langlands.GroupScheme.SimplyConnected.LocalOuterTypeAHermitianModelStatement`).
It does not prove either proposition outright.

## `IsNonarchimedeanLocalField.infinite`

Full name `Langlands.GroupScheme.IsNonarchimedeanLocalField.infinite`: every
field `K` with `[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
is infinite.

Proof: the valuation is nontrivial (`ValuativeRel.IsNontrivial`, part of
`IsNonarchimedeanLocalField`), so some value `γ` has `0 < γ < 1`; write
`γ = v(r)` with `r ≠ 0`. If `K` were finite, `r` would be a unit of the
finite group `Kˣ`, so `r ^ m = 1` for `m = Nat.card Kˣ > 0`
(`pow_card_eq_one'`). Then `v(r) ^ m = 1`, contradicting `v(r) ^ m < 1`
(`pow_lt_one₀`).

## `localAnisotropicTypeAInner_of_hermitianModel`

`(h : LocalOuterTypeAHermitianModelStatement.{u}) : LocalAnisotropicTypeAInnerStatement.{u}`,
at every universe `u`, with no further hypotheses.

Proof: take `K`, `G`, `d`, `n` and the hypotheses `IsSimplyConnected G`,
`IsAbsolutelyAlmostSimple G`, `IsAnisotropic G` and the type-`A_n` numbering.
Suppose, for contradiction, that `d.star σ a ≠ a` for some `σ` and `a`. Then
`h` applies (it does not need anisotropy) and gives a separable quadratic
extension `L`, a diagonal form `H` with unit weights `w`, and an isomorphism
`e : G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`. Let
`χ = HermitianRoot.SchemeModel.cocharacter K L H w hw`. Since `G` is affine and
anisotropic, the published `IsAnisotropic.cocharacter_eq_zero` gives
`χ ≫ e.inv = 0`, hence `χ = χ ≫ e.inv ≫ e.hom = 0`. But `K` is infinite
(previous lemma), so `HermitianRoot.SchemeModel.cocharacter_ne_zero`
(module `Langlands.GroupScheme.Examples.HermitianRootCocharacterNontrivial`) says
`χ ≠ 0`. This contradiction proves `d.star σ a = a` for all `σ` and `a`.

No restriction on the characteristic of `K` or of its residue field is used.
The route is the first argument of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §10.3, paragraph after Remark 10.3.2, printed pp. 392–393 /
PDF pp. 423–424: an outer form of type `A_n`, `n ≥ 2`, is `SU(h)` for an
isotropic Hermitian form `h`, hence isotropic; here isotropy is witnessed by
the explicit diagonal cocharacter of the hyperbolic plane in the model.
