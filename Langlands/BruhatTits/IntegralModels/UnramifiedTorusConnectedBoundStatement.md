# Integral points of connected torus models lie in the Iwahori subgroup

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundStatement.{u}`
is an unproved proposition. It is one of three focused torus inputs of
`UnramifiedTorusIwahoriModelAssemblyStatement`. It contains the deep part
of the source: the norm description of the integral points of the connected
Néron model. This module proves nothing.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page numbers are followed by PDF page numbers.

- Definition 2.5.13, printed p. 90 / PDF p. 121: `T(K)^0` is the image of
  `T(L)^b` under the norm `T(L) → T(K)`, for a finite Galois extension
  `L/K` splitting `T`.
- Remark B.8.5, printed p. 682 / PDF p. 713: a homomorphism from a smooth
  affine `o`-group to the generic fibre extends to `T^ft`. If the source has
  connected fibres, the extension factors through the relative identity
  component `T^0`.
- Corollary B.8.6, printed pp. 682–683 / PDF pp. 713–714, and Corollary
  B.8.7 with its proof, printed p. 683 / PDF p. 714: `T^0(O) = T(K)^0`.
- Proof of Proposition B.8.8(3), printed pp. 683–684 / PDF pp. 714–715: for
  a smooth model `T_1` with connected fibres, the generic isomorphism extends
  to `T_1 → T^ft`, factors through `T^0`, and therefore maps `T_1(O)` into
  `T(K)^0` by Corollary B.8.7.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, amend Appendix B only in Section B.10. PDF pp. 24–25 correct Section 2.5 only by the sign convention of `ω_T` in
2.5(b), which leaves its kernel unchanged, a cross-reference in Remark
2.5.11 and the replacement of Remark 2.5.15. They do not change Proposition
2.5.8, Lemma 2.5.12 or Definition 2.5.13.

## Exact statement

For every nonarchimedean local field `F : Type u`, write
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. Take an actual
commutative group scheme `T` over `Spec K` with affine underlying scheme and
an actual intermediate field `L` of `SeparableClosure F / K`, finite and
Galois over `K`, such that `baseChanged K L T.toGrp` is a split torus. Then
for every

```text
M : IntegralModel O K T.toGrp
```

with `M.IsSmooth` and `M.HasGeometricallyConnectedFibres`,

```text
M.integralPoints ≤
  torusNormIwahori K L (intermediateValuation F L) T.
```

`M.HasGeometricallyConnectedFibres` is Mathlib's `GeometricallyConnected`
for the actual structure morphism of `M.group`. `torusNormIwahori` is the
image, under the actual rational norm `T(L) → T(K)`, of the common kernel
of the character valuations of `T_L` for the valuation
`intermediateValuation F L` of `L`. This is `T(K)^0` of Definition 2.5.13.

## Scope and derivation

The source proves the equality `T^0(O) = T(K)^0` for its specific connected
Néron model and deduces the bound for every smooth model with connected
fibres in the proof of Proposition B.8.8(3). The statement records that
bound for every smooth affine model in the `IntegralModel` sense with
geometrically connected fibres. For a smooth group over a field,
geometric connectedness and connectedness agree, so the hypothesis is the
source's connected-fibre hypothesis. The statement is a derived
formulation; it asserts no existence of a model, no Néron mapping
property and no equality.

Over `K` the source's `O` is `fixedFieldIntegers F` itself, since its residue
field is algebraically closed. `K` and `O` need not be complete. The
inclusion holds for each supplied splitting field `L`; the independence of
`T(K)^0` from `L` is not used.
