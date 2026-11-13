# The torus Iwahori subgroup as an image of a connected smooth model

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageStatement.{u}`
is an unproved proposition. It is one of three focused torus inputs of
`UnramifiedTorusIwahoriModelAssemblyStatement`. It supplies the
connectedness half of the target: `T(K)^0` is the image of the integral
points of a smooth model with geometrically connected fibres. This module
proves nothing.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page numbers are followed by PDF page numbers.

- Definition 2.5.13, printed p. 90 / PDF p. 121: `T(K)^0` is the image of
  `T(L)^b` under the norm `T(L) → T(K)`, which is the map on `K`-points of
  the algebraic norm `R_{L/K}(T_L) → T` (Lemma 2.5.12, printed pp. 89–90 /
  PDF pp. 120–121).
- Section B.3 and Lemma B.3.1, printed pp. 656–657 / PDF pp. 687–688: for a
  finite separable extension `ℓ/k`, the model `R_{o_ℓ/o}(G_m)` of
  `R_{ℓ/k}(G_m)` is smooth with geometrically connected special fibre
  (B.3.1(1)), and its `O`-points are the maximal bounded subgroup of the
  `K`-points (B.3.1(2)).
- Proof of Corollary B.8.7, printed p. 683 / PDF p. 714: with
  `S = R_{L/K}(T_L)` and the norm `S → T`, `T(K)^0` is the image of
  `S(K)^0 = S^0(O)`.

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
Galois over `K`, such that `baseChanged K L T.toGrp` is a split torus. The
proposition asserts that there exist

- a group scheme `S` over `Spec K`,
- an integral model `W : IntegralModel O K S`, and
- a homomorphism of group schemes `n : S ⟶ T.toGrp`,

such that `W.IsSmooth`, `W.HasGeometricallyConnectedFibres`, and

```text
W.integralPoints.map (rationalPoints.map n) =
  torusNormIwahori K L (intermediateValuation F L) T.
```

The right side is `T(K)^0` of Definition 2.5.13: the image under the actual
rational norm of the common kernel of the character valuations of `T_L`.
The left side is the image of the integral-point subgroup of `W` under the
map of rational points induced by `n`.

## Intended witness and scope

In the source, `S = R_{L/K}(T_L)`, `n` is the algebraic norm, and `W` is the
Weil restriction from the integers of `L` to `O` of a split torus model of
`T_L`. Lemma B.3.1 gives smoothness and the connected special fibre, and the
`O`-points of `W` are the bounded subgroup `T(L)^b` of `S(K) = T(L)`. The
Library has the actual Weil restriction `AffineWeil.groupScheme`, its
smoothness, and the algebraic norm `GaloisNorm.norm`.

The proposition is a derived existential form of these facts. It records
only what the assembly needs and does not fix the witness.
`HasGeometricallyConnectedFibres` concerns every fibre of the structure
morphism, including the generic one. For the source witness, the generic
condition is geometric connectedness of the torus `R_{L/K}(T_L)`, and the
special one is Lemma B.3.1(1). No root, apartment,
building or reductive ambient-group datum is involved. `K` and `O` need not
be complete.
