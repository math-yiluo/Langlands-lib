# Smooth models of the maximal bounded torus subgroup

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelStatement.{u}`
is an unproved proposition. It is one of three focused torus inputs of
`UnramifiedTorusIwahoriModelAssemblyStatement`, which reduces
`UnramifiedTorusIwahoriModelStatement` to them and to the published
extension criterion `IntegralModel.SmoothHomExtensionStatement`. This
module proves nothing.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page numbers are followed by PDF page numbers.

- Proposition 2.5.8, printed p. 88 / PDF p. 119: a `k`-torus `T` has a
  unique maximal bounded subgroup `T(k)^b = T(k)^1`, the set of `x` with
  `ω(χ(x)) = 0` for every `k`-rational character `χ`.
- Definition B.7.1 and Proposition B.7.2, printed p. 675 / PDF p. 706, with
  the proof on printed p. 676 / PDF p. 707: the ft-Néron model `T^ft` is the
  smoothening of the standard model, and B.7.2(2) states
  `T^ft(O) = T^std(O) = T(K)^1`.
- Corollary B.7.4, printed p. 676 / PDF p. 707: `T(K)^1` is schematic.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, amend Appendix B only in Section B.10, so Proposition B.7.2
is unchanged. PDF pp. 24–25 correct Section 2.5 only by the sign convention of `ω_T` in
2.5(b), which leaves its kernel unchanged, a cross-reference in Remark
2.5.11 and the replacement of Remark 2.5.15. They do not change Proposition
2.5.8, Lemma 2.5.12 or Definition 2.5.13.

## Exact statement

For every nonarchimedean local field `F : Type u`, write
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. These are the
Library's maximal unramified subfield of `SeparableClosure F` and its
valuation ring. For every actual commutative group scheme `T` over `Spec K`
with affine underlying scheme and with `IsTorus T.toGrp`, the proposition
asserts the existence of

```text
M : IntegralModel O K T.toGrp
```

with `M.IsSmooth` and the literal subgroup equality

```text
M.integralPoints = characterValuationKernel (fixedFieldValuation F) T.toGrp
```

in `rationalPoints T.toGrp`.

`IsTorus T.toGrp` is the Library predicate: some base change of `T` to a
field extension of `K` is a split torus. `characterValuationKernel` is the
common kernel of the valuations of all rational characters of `T`, the
second description of `T(K)^b = T(K)^1` in Proposition 2.5.8, written
multiplicatively. `fixedFieldValuation F` is the restriction to `K` of the
valuation of `SeparableClosure F`, and `O` is its valuation subring.
`IntegralModel` supplies an affine, flat, locally finite type group scheme
over `O` with a specified generic isomorphism to `T.toGrp`.
`M.integralPoints` is the image of the integral sections under that
isomorphism.

## Scope

The source works over `K` for every Henselian discretely valued `k`. The
statement is the case `k = K` for the maximal unramified extension of a
nonarchimedean local field, the base used throughout Chapter 8 of the
source. `K` and `O` need not be complete. Only the integral-point equality
of B.7.2(2) and smoothness are asserted. The coordinate-ring description
B.7.2(3), the descent statement B.7.2(1), the ft-Néron mapping property
of Proposition B.8.4(1) and uniqueness are not asserted. The model is
existentially quantified and need not be the source's specific `T^ft`.

## Expected proof route

The source smoothens the standard model, using Appendix A. In the Library,
the published `MaximalBoundedIntegralModelStatement`
(`Langlands.GroupScheme.IntegralModel.MaximalBounded`, proof task Task
6167) gives a smooth model of any maximal algebraically bounded subgroup.
Combined with maximality of `T(K)^1` among bounded subgroups (Proposition
2.5.8) and the identification of `O` with the canonical integer ring of
`K`, it would prove this proposition. Neither input is proved here.
