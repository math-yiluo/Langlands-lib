# Base change of cocharacters and of the dynamic subgroup functors

This module base-changes a cocharacter `λ : 𝔾_{m,S} ⟶ G` along an arbitrary morphism of base
schemes `b : S' ⟶ S`. It shows that the dynamic subgroup functors `P_G(λ)`, `Z_G(λ)` and
`U_G(λ)` of `Langlands.GroupScheme.Dynamic.Basic` commute with this base change. `G` is an
arbitrary group scheme over `S`, with no affineness, finiteness or separatedness hypothesis.
The comparison is made on the subfunctors of points, on all test schemes `T'` over `S'`.

## Sources

- Conrad, *Reductive group schemes* (2014), p. 114, the paragraph after Example 4.1.9: "It is
  immediate from the definitions that the formation of `P_G(λ)`, `U_G(λ)`, `Z_G(λ)` commutes
  with any base change on `k`, and Theorem 4.1.7 adapts to any base scheme `S`". The definitions
  are those of Definition 4.1.6 and Theorem 4.1.7 (pp. 112–113).

Conrad states the remark for a finitely presented affine group `G` over a ring `k` with an
abstract `𝔾_m`-action, and for the schemes that represent the functors. This module covers
the conjugation action of a cocharacter on an arbitrary group scheme over an arbitrary base,
and compares subfunctors of points. It proves no representability.

## Notation

`GroupScheme.baseChange b` is the Library base-change functor along `b`.
`baseChangePointsEquiv b G T'` is the Library pullback equivalence between the points
`T' ⟶ G_{S'}` and the points `T' ⟶ G` over `S`, where `T'` is viewed over `S` through `b`
(`Over.map b`). `SubgroupFunctor.baseChange b F` is the Library subgroup functor of `G_{S'}`
whose `T'`-points are the points that this equivalence sends into `F`.

## Comparison of test schemes

- `Dynamic.pullbackPullbackSndIso f b x` is the canonical isomorphism
  `T ×_{S'} (X ×_S S') ≅ T ×_S X` in any category with pullbacks. It comes with its two
  projection lemmas.
- `Dynamic.mapTensorPullbackIso b T' X` is the same isomorphism for `T'` over `S'` and `X`
  over `S`, written as an isomorphism `T' ×_{S'} X_{S'} ≅ T' ×_S X` of schemes over `S`
  (products are the cartesian monoidal products of `Over S'` and `Over S`). Its first
  projection is the first projection of `T' ×_{S'} X_{S'}` (`mapTensorPullbackIso_hom_fst`).
  Its second projection is the second projection followed by `X_{S'} ⟶ X`
  (`mapTensorPullbackIso_hom_snd_left`).
- `Dynamic.mapTensorIso b T' i` replaces `X_{S'}` by any `X'` with an isomorphism
  `i : X' ≅ X_{S'}`. It has the analogous projection lemmas `mapTensorIso_hom_fst` and
  `mapTensorIso_hom_snd_left`.
- `AffineLine.baseChangeIso b : 𝔸¹_{S'} ≅ (𝔸¹_S)_{S'}` comes from Mathlib's pullback square
  `AffineSpace.isPullback_map`. `baseChangeIso_appTop_coord` says that the composite
  `𝔸¹_{S'} ⟶ 𝔸¹_S` pulls the coordinate of `𝔸¹_S` back to the coordinate of `𝔸¹_{S'}`.
- `AffineLine.mapTensorIso b T' : T' ×_{S'} 𝔸¹_{S'} ≅ T' ×_S 𝔸¹_S` preserves the coordinate
  function (`homEquiv_mapTensorIso_hom_snd`).
- `Gm.overBaseChangeIso b : 𝔾_{m,S'} ≅ (𝔾_{m,S})_{S'}` is the inverse of the Library
  isomorphism `Gm.baseChangeIso b`, as schemes over `S'`.
  `Gm.mapTensorIso b T' : T' ×_{S'} 𝔾_{m,S'} ≅ T' ×_S 𝔾_{m,S}` preserves the unit coordinate
  (`mapTensorIso_hom_snd` and `pointsEquiv_mapTensorIso_hom_snd`).
- `Dynamic.mapTensorIso_unitInclusion`: the two comparisons are compatible with the
  inclusions `T' ×_{S'} 𝔾_{m,S'} ⊆ T' ×_{S'} 𝔸¹_{S'}` and `T' ×_S 𝔾_{m,S} ⊆ T' ×_S 𝔸¹_S`.
- `Dynamic.mapTensorIso_zeroSection`: the comparison for `𝔸¹` sends the zero section
  `T' ⟶ T' ×_{S'} 𝔸¹_{S'}` to the zero section `T' ⟶ T' ×_S 𝔸¹_S`.

The proofs reduce to the coordinate descriptions of morphisms to `𝔸¹` and to `𝔾_m`
(`AffineLine.hom_ext`, `AffineLine.homEquiv`, `Gm.pointsEquiv`) and to the projection
lemmas above.

## The base-changed cocharacter

- `Dynamic.baseChangeCocharacter b χ : 𝔾_{m,S'} ⟶ G_{S'}` is `(Gm.baseChangeIso b).inv`
  followed by the base change of `χ`. This is `λ_{S'}` in Conrad's notation.
- `baseChangePointsEquiv_baseChangeCocharacter`: on points, `λ_{S'}` applied to a unit is `λ`
  applied to the same unit.

## Orbits, extensions and limits

Fix `T'` over `S'` and a point `g : T' ⟶ G_{S'}`. Write `g_S` for the point
`baseChangePointsEquiv b G T' g : T' ⟶ G` over `S`. The notions are those of
`Dynamic.Basic`.

- `baseChangePointsEquiv_orbit`: the orbit map of `g` under `λ_{S'}` corresponds, along
  `Gm.mapTensorIso b T'`, to the orbit map of `g_S` under `λ`.
- `isOrbitExtension_baseChange_iff`: a morphism `e : T' ×_{S'} 𝔸¹_{S'} ⟶ G_{S'}` extends the
  orbit map of `g` under `λ_{S'}` if and only if the corresponding morphism
  `T' ×_S 𝔸¹_S ⟶ G`, namely `(AffineLine.mapTensorIso b T').inv` followed by the image of `e`
  under `baseChangePointsEquiv`, extends the orbit map of `g_S` under `λ`. The proof uses that
  `baseChangePointsEquiv` is injective, that it is natural, `baseChangePointsEquiv_orbit` and
  `mapTensorIso_unitInclusion`.
- `baseChangePointsEquiv_evalZero`: evaluating `e` at zero and then passing to `S` gives the
  value at zero of the corresponding morphism over `S` (from `mapTensorIso_zeroSection`).
- `hasLimit_baseChange_iff`: `g` has limit `l` under `λ_{S'}` if and only if `g_S` has limit
  `l_S` under `λ`. Extensions are transported in both directions with the bijections
  `baseChangePointsEquiv` and `AffineLine.mapTensorIso b T'`.

## The dynamic subgroup functors commute with base change

These are equalities of `SubgroupFunctor`s of `G_{S'}`. Each is proved by extensionality on
`T'`-points.

- `parabolic_baseChange`: `P_{G_{S'}}(λ_{S'}) = P_G(λ)_{S'}`, from
  `isOrbitExtension_baseChange_iff`.
- `centralizer_baseChange`: `Z_{G_{S'}}(λ_{S'}) = Z_G(λ)_{S'}`, from
  `baseChangePointsEquiv_orbit`. The constant orbit map corresponds to the constant orbit map.
- `unipotent_baseChange`: `U_{G_{S'}}(λ_{S'}) = U_G(λ)_{S'}`, from `hasLimit_baseChange_iff`
  and the fact that `baseChangePointsEquiv` sends `1` to `1`.

These three equalities are Conrad's remark for the conjugation action and at the level of
functors of points. When the functors are representable, this gives the comparison of the
representing schemes by Yoneda. That step is not formalized here.
