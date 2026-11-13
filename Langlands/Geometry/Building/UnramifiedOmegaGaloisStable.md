# Galois stability of centralizer-compatible apartment classes over an extension

This module removes the hypotheses of the existing theorem
`IntegerValuation.IsOmegaCompatible.galoisStable` (module
`IntegerOmegaGaloisStability`) that are not part of the data. That theorem needs
two things: V6 for one particular scalar-extended centralizer datum, and actual
opposite factor pairs upstairs. Here V6 for *any* centralizer datum of the
scalar-extended torus is enough, and the opposite pairs come from the published
rank-one factorization. The application is to the maximal unramified extension
`K` of a nonarchimedean local field `F`. There, every V6 class of valuations of the
root datum of `(G_K, T_K)` is stable under `Aut(K/F)`, where `T` is an `F`-subgroup
whose scalar extension is a maximal `K`-split torus. This is the Lean form of the
remark in Kaletha–Prasad (2023), §9.2.1–§9.2.2 (printed p. 326, PDF p. 357): if
`T_K` is defined over `k`, the apartment `A_T` is stable under `Γ = Aut(K/k)`.
KP deduce this from the compatible `Γ`-actions on `B(G_K)` and `G(K)`
(their Proposition 7.9.5). Here an apartment is a class of valuations of the root
datum. The published proof of `IsOmegaCompatible.galoisStable` shows that the
`Γ`-conjugate of a V6 class for a scalar-extended centralizer datum is again a
V6 class for the same datum (`CentralizerGaloisTransport`). It then applies the uniqueness of V6 classes
(`IsOmegaCompatible.eq_of_hasOppositeFactorPairs`, `IntegerOmegaApartmentRigidity`).

All results are internal consequences of existing definitions and published
theorems. No new definition or statement is introduced.

## Independence of the centralizer representative

Let `k` be a field, `v : Valuation k ℤₘ₀`, `S` a commutative group scheme over
`k`, `G` a group scheme over `k` and `i : S.toGrp ⟶ G`. Let `C` and `E` be two
`CentralizerDatum i`. Both `C.j` and `E.j` represent the same subgroup functor
`torusCentralizer i`, so `C.isRepresentedBy.isoOfIsRepresentedBy E.isRepresentedBy`
gives an isomorphism `e : C.Z ≅ E.Z` with `e.hom ≫ E.j = C.j`.

- `centralizerTranslation_comparison v C E z` states that the integer-valued
  translation vector `centralizerTranslation v C.s C.bijective z` of a point
  `z ∈ C.Z(k)` equals the translation vector of `e(z) ∈ E.Z(k)` computed with
  `E`. First `C.s ≫ e.hom = E.s`, by `E.isRepresentedBy.hom_ext` and both
  `comp_eq` fields. By injectivity of `Cartan.restrictionEvaluation E.s`
  (`E.bijective`) it suffices to compare evaluations on the restriction of every
  rational character `χ` of `E.Z`. The restriction of `χ` along `E.s` equals the
  restriction of `characterRestrict e.hom χ` along `C.s`. The published
  `eval_centralizerTranslation` turns both sides into
  `-order v (rationalCharacterEval _ _)`. These agree by
  `rationalCharacterEval_characterRestrict`. The argument is the same as for the
  published local-field lemma `CentralizerDatum.comparisonIso_translation`, here
  for an arbitrary integer-valued valuation.
- `IsOmegaCompatible.of_centralizerDatum v E hD` assumes
  `[Mono i.hom.hom.left]`, `[IsAffineHom G.X.hom]`, `D : KPApartmentData i (order v)`
  and `hD : IsOmegaCompatible v D C`, and concludes
  `IsOmegaCompatible v D E`. Every point of `E.Z(k)` has the form `e(z)`, because
  `isoPointsEquiv e` is bijective. Also `E.j(e(z)) = C.j(z)` and the translation
  vectors agree, so each instance of V6 for `E` is an instance of V6 for `C`.
  `isOmegaCompatible_iff_centralizerDatum v C E` records both directions. This
  is the integer-valued analogue of the published
  `KPApartmentData.IsOmegaCompatible.of_centralizerDatum`, which covers only the
  local-field order over the base field.

## Galois stability over an arbitrary extension

Let `k ⊆ K` be fields in any universe `u`, `T` a commutative group scheme over
`k` that is affine over the base (`[IsAffineHom T.X.hom]`), `G` a group scheme
over `k` affine over the base, and `i : T.toGrp ⟶ G`. Write `T_K`, `G_K`, `i_K`
for the scalar extensions along `algebraBaseMap k K`, and assume
`[Mono i_K.hom.hom.left]`. Let `w : Valuation K ℤₘ₀` and assume

- `hw`: `order w (σ t) = order w t` for every `σ : K ≃ₐ[k] K` and `t ∈ Kˣ`,
- `hG : IsConnectedReductive G_K` and `hi : IsMaximalSplitTorus i_K`,
- `D : KPApartmentData i_K (order w)`, `C : CentralizerDatum i_K` and
  `hD : IsOmegaCompatible w D C`.

`IntegerValuation.IsOmegaCompatible.galoisStable_of_centralizerDatum` concludes
`KPApartmentData.GaloisStable k K i D`. The proof:

1. `fieldCentralizerRepresentability` gives a closed subgroup `j : Z ⟶ G` over
   `k` representing `torusCentralizer i`. Let `s = torusCentralizerFactor i hj`,
   so that `s ≫ j = i`.
2. After scalar extension, `j_K` is a closed subgroup (`IsClosedSubgroup.baseChange`).
   It represents `torusCentralizer i_K`, by the published
   `torusCentralizer_baseChange` and `IsRepresentedBy.baseChange`. Also
   `s_K ≫ j_K = i_K` by functoriality.
3. `Cartan.restrictionEvaluation s_K` is bijective. This is the published
   `Cartan.restrictionEvaluation_bijective_of_torusCentralizer`, valid over every
   field for the represented centralizer of a maximal split torus of a connected
   reductive group.
4. These data form a `CentralizerDatum i_K`, called `E`. By
   `IsOmegaCompatible.of_centralizerDatum`, V6 for `C` gives V6 for `E`.
5. `RelativeRoot.HasOppositeFactorPairs i_K` follows from the published
   `rootRankOneFactorization` and
   `RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs`. Their
   inputs are smoothness of `G_K` (from `hG`) and splitness of `T_K` (from `hi`).
   The smoothness instance is passed explicitly, to avoid an expensive instance
   search through the base-change presentation of `G_K`.
6. The published `IntegerValuation.IsOmegaCompatible.galoisStable` then applies,
   with this `Z`, `j`, `s` and `E`.

## The maximal unramified extension

Let `F` be a nonarchimedean local field, and `K = inertiaFixedField F` with its
normalized integer valuation `MaximalUnramified.valuation F`.

- `fixedFieldValuation_galois F σ x`: the spectral valuation `fixedFieldValuation F`
  is invariant under every `σ : K ≃ₐ[F] K`. It equals the spectral valuation of
  `K/F` (`fixedFieldValuation_eq_spectralValuation`), and Mathlib's
  `spectralNorm_eq_of_equiv` states that `F`-automorphisms preserve the spectral
  norm.
- `valuation_galois F σ x`: `valuation F (σ x) = valuation F x`. The two valuations
  are equivalent (`valuation_isEquiv`), so the inequalities in both directions
  transfer from `fixedFieldValuation F`.
- `order_galois F σ t`: the real order `IntegerValuation.order (valuation F)` is
  `Aut(K/F)`-invariant on units. Unfold the order with `orderUnits_toAdd` and
  use `valuation_galois`.

Finally, `MaximalUnramified.galoisStable_of_isOmegaCompatible iT hiTc hGK hiT D C hD`
has implicit `F`, `G` (with `[IsAffineHom G.X.hom]`) and `T`, and
`[Mono i_K.hom.hom.left]` for `i_K` the scalar extension of `iT` along
`algebraBaseMap F (inertiaFixedField F)`. Its hypotheses are:

- `hiTc : IsClosedSubgroup iT`,
- `hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G)`,
- `hiT : IsMaximalSplitTorus i_K`,
- `D : KPApartmentData i_K (IntegerValuation.order (valuation F))`,
  `C : CentralizerDatum i_K` and `hD : IntegerValuation.IsOmegaCompatible (valuation F) D C`.

It concludes `KPApartmentData.GaloisStable F (inertiaFixedField F) iT D`. The
closed-subgroup hypothesis is used only to make `T` affine over `F`, via
`IsClosedSubgroup.isAffineHom`; that is needed to represent the centralizer of
`T` over `F`. The special tori of the published `SpecialTorusExistenceStatement`
(KP Proposition 9.3.4) are closed subgroups, so this hypothesis is available
there. The proof is the general theorem with `w = valuation F` and
`hw = order_galois F`.
