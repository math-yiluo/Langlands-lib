# Centralizing the rational points of a split torus

Authors: Worker 88, with Worker 2094 (route).

Lean module: `Langlands.Geometry.Building.TwistedFixedTranslationCentralizer`.

This module is a helper for the proof of `UnramifiedTwistedFixedTranslationStatement`
(Kaletha–Prasad, Proposition 9.3.13, first paragraph of the proof). That statement assumes
that `h ∈ G(K)` commutes with the `K`-points of the maximal `F`-split torus `S`. The proof needs
the scheme-level form of this hypothesis: conjugation by `h` fixes the base-changed embedding
`S_K → G_K`. This is the standard fact that a point centralizing a Zariski-dense set of points
of a reduced subgroup centralizes the whole subgroup. The module records it in the form used
in the proof. It is not a numbered result of KP.

## Statement

- `comp_innerIso_eq_of_commute`: let `k` be a field, `K` an infinite field extension of `k`,
  `S` a commutative `k`-group scheme, `G` a `k`-group scheme with separated structure morphism,
  and `iS : S → G` a homomorphism. Assume that the base change `S_K` is a split torus. Let
  `h ∈ G(K)` commute with `iS(s)` for every `s ∈ S(K)`. Then
  `iS_K ≫ Int(h) = iS_K`, where `iS_K : S_K → G_K` is the base change of `iS` and `Int(h)`
  is the inner automorphism `G_K.innerIso h` of `G_K`.

  The commutation hypothesis is stated with `baseChanged k K` and `baseMap k K`, as in the
  target statement. The conclusion uses `algebraBaseMap k K`. Both names abbreviate the same
  morphism `Spec K → Spec k`.

## Proof

- The underlying scheme of the split torus `S_K` is integral (published
  `IsSplitTorus.isIntegral`), so it is reduced. The structure morphism of `G_K` is a pullback
  of that of `G`, so it is separated.
- The `K`-points of `S_K` are Zariski dense. This is the published
  `TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange`, applied to the trivial
  extension `K/K` and to `S_K`, which stays split after the trivial base change
  (`IsSplitTorus.baseChange`). It needs `K` infinite.
- By `Grp.hom_ext` it suffices to compare the underlying scheme morphisms `S_K → G_K`. By the
  published `hom_ext_of_denseRationalPoints` (reduced source, separated target, dense
  rational points), it suffices to compare them on each `K`-point `p` of `S_K`.
- On such a point, `p ≫ iS_K ≫ Int(h)` equals `h · iS_K(p) · h⁻¹` (published
  `comp_innerIso_hom` together with `constantPoint_self`). This equals `iS_K(p)` because `h`
  commutes with `iS_K(p)` by hypothesis.
