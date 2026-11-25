# Injectivity of the finite local components of idele cohomology in degree two

Let `E / F` be a Galois extension of number fields and `J_E` the idele group
of `E`, with the published Galois representation
`relativeIdeleRepresentation F E`. For finite places `w | v`, the published
`ideleLocalMap v w 2` sends `H²(Gal(E/F), J_E)` to
`H²(Gal(E_w/F_v), E_wˣ)`. This module proves: let `f` be a 2-cocycle of
`J_E` whose values all have infinite adele part `1`, and choose one place
`wf v` over each finite place `v` of `F`. If `ideleLocalMap v (wf v) 2` kills
the class of `f` for every finite place `v`, then the class of `f` is zero.

The module assumes that each `H²(Gal(E_w/F_v), E_wˣ)` is finite with at most
`[E_w : F_v]` elements, as in the published `IdeleLocalSupport` and
`LocalUnitVanishing` modules. That assumption is part of local class field
theory and is not proved here.

Only finite places and degree `2` are treated. The infinite places enter only
through the hypothesis that the cocycle has infinite adele part `1`. The
module does not show that every class has such a representative, and it does
not treat the archimedean local maps.

## Places below and conjugate places

Let `F` and `E` be number fields with `E` an `F`-algebra.

- `placeBelow F w`, for a finite place `w` of `E`, is the finite place of `F`
  with prime ideal `w ∩ 𝓞 F` (Mathlib's `Ideal.under`). This prime is nonzero
  by Mathlib's `Ideal.under_ne_bot`. The instance `liesOver_placeBelow` says
  that `w` lies over `placeBelow F w`.
- `placeBelow_eq`: if `w` lies over `v`, then `placeBelow F w = v`.
- `liesOver_finitePlaceEquiv`: if `w` lies over `v` and `g ∈ Gal(E/F)`, then
  the published `finitePlaceEquiv g.toRingEquiv w` also lies over `v`,
  because `g` fixes `𝓞 F`.
- `exists_finitePlaceEquiv_eq`: for `E / F` Galois, `Gal(E/F)` acts
  transitively on the finite places over `v`: if `w` and `w'` lie over `v`,
  then `finitePlaceEquiv g.toRingEquiv w = w'` for some `g`. This is
  Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`.

## Ideles from coordinates

- `idele_ext`: two ideles of `E` are equal if their infinite adele parts are
  equal and their coordinates `ideleCoordinate w` (published) agree at every
  finite place `w`.
- `eventually_mem_adicCompletionIntegers`: let `a w ∈ E_wˣ` for every finite
  place `w`, with `a w` in the published valuation units `localUnits w` for
  all but finitely many `w`. Then `a w` is integral for all but finitely many
  `w`.
- `ideleOfCoordinates a ha`, for such a family `a` (with `ha` the finiteness
  of `{w | a w ∉ localUnits w}`), is the idele with infinite adele part `1`
  and coordinate `a w` at every finite place `w`. Its finite adele and that of
  its inverse are given by Mathlib's `RestrictedProduct.mk`, using the
  previous lemma for `a` and for `a⁻¹`.
  `ideleCoordinate_ideleOfCoordinates` gives the coordinates and
  `ideleOfCoordinates_infinite` the infinite part.
- `ideleInfiniteTrivial` is the subgroup of ideles of `E` with infinite adele
  part `1`. `mem_ideleInfiniteTrivial_iff` unfolds membership.
- `relativeIdeleAut_mem_ideleInfiniteTrivial`: the action of each
  `g ∈ Gal(E/F)` (the published `relativeIdeleAut F E g`) preserves this
  subgroup. On infinite adeles the action is a ring isomorphism, so it fixes
  `1`.
- `ideleCoordinate_relativeIdeleAut`: the `w`-coordinate of `g • x` is the
  published `finiteCompletionEquiv g.toRingEquiv w` applied to the coordinate
  of `x` at `finitePlaceEquiv g.toRingEquiv w`. This holds by definition.

## Coordinates over one place of `F`

Fix a finite place `v` of `F`. The next lemmas compare ideles through their
coordinates at the places over `v`.

- `ideleCoordinate_relativeIdeleAut_eq`: if `x` and `y` have equal
  coordinates at every place over `v`, then so do `g • x` and `g • y`, for
  every `g ∈ Gal(E/F)`.

The rest of this section assumes that `E / F` is Galois and `w` lies over `v`.
`ideleSemilocalProjection v w : J_E ⟶ Coind(E_wˣ)` and
`ideleSemilocalSection v w : Coind(E_wˣ) ⟶ J_E` are the published semilocal
projection and section, with coinduction along `decompositionHom v w`.

- `ideleSemilocalProjection_apply`: the value at `g` of the semilocal
  projection of `x` is the `w`-coordinate of `g • x`. This holds by
  definition.
- `ideleCoordinate_eq_of_ideleSemilocalProjection_eq`: if `x` and `y` have
  the same semilocal projection at `w`, then they have the same coordinates
  at every place `w'` over `v`. Write `w' = g w`, using transitivity. The
  `w`-coordinates of `g • x` and `g • y` agree, and
  `finiteCompletionEquiv g.toRingEquiv w` is injective.
- `ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection`: if every value
  of the semilocal projection of `x` at `w` lies in `localUnits w`, then every
  coordinate of `x` at a place over `v` is a valuation unit. Again write
  `w' = g w`. The published `finiteCompletionEquiv_valuation` says that
  `finiteCompletionEquiv` preserves valuations.

The next two lemmas also assume
`[Fintype (Gal(E/F) ⧸ (decompositionHom v w).range)]`, which the semilocal
section needs.

- `ideleSemilocalProjection_ideleSemilocalSection`: the semilocal projection
  of the semilocal section of `β` is `β`. This is the published
  `ideleSemilocalSection_comp_ideleSemilocalProjection`.
- `ideleCoordinate_ideleSemilocalSection_ideleSemilocalProjection`: the
  semilocal section of the semilocal projection of `x` has the same
  coordinates as `x` at every place over `v`. This follows from the two
  previous lemmas.

## Coinduced valuation units

Let `E / F` be normal and `w | v`. The published `localUnitsRepresentation v w`
is the representation of `Gal(E_w/F_v)` on `localUnits w`.

- `coindLocalUnitsInclusion v w : Coind(U_w) ⟶ Coind(E_wˣ)` is Mathlib's
  `Rep.coindMap` of the published inclusion `localUnitsInclusion v w`, with
  coinduction along `decompositionHom v w`.
- `coindLocalUnitsInclusion_injective`: it is injective on carriers.
- `exists_coindLocalUnitsInclusion_eq`: an element of `Coind(E_wˣ)` all of
  whose values lie in `localUnits w` is the image of an element of
  `Coind(U_w)`.
- `isZero_H2_coindLocalUnits`: let `E / F` be Galois and `w` have
  ramification index `1` over `F`. Assume that `H²(Gal(E_w/F_v), E_wˣ)` is
  finite with at most `[E_w : F_v]` elements. Then
  `H²(Gal(E/F), Coind(U_w)) = 0`. The published Shapiro isomorphism
  `Shapiro.shapiroIsoOf` (for the injective `decompositionHom v w`) identifies
  this group with `H²(Gal(E_w/F_v), U_w)`. That group is zero by the
  published `isZero_H2_localUnits`.

## Local primitives

Let `E / F` be Galois, `w | v`, and `f` a 2-cocycle of `J_E`.

- `exists_d₁₂_eq_ideleSemilocalProjection`: if `ideleLocalMap v w 2` kills the
  class of `f`, then there is a 1-cochain `β` with values in `Coind(E_wˣ)`
  whose coboundary is the semilocal projection of `f`, that is,
  `d β (g, h) = P (f (g, h))` for `P = ideleSemilocalProjection v w`. By the
  published `ideleLocalMap_eq`, the local map is the map induced by `P`
  followed by the Shapiro map. The Shapiro map is injective by the published
  `Shapiro.isIso_shapiroMapOf`, so `P` kills the class of `f`. Mathlib's
  `groupCohomology.H2π_eq_zero_iff` gives `β`.
- `exists_d₁₂_eq_ideleSemilocalProjection_units`: assume moreover that `w`
  has ramification index `1`, that `H²(Gal(E_w/F_v), E_wˣ)` is finite with at
  most `[E_w : F_v]` elements, and that every value of `f` has
  valuation-unit coordinates at all places over `v`. Then `β` can be chosen
  with all its values in `localUnits w`. No vanishing of the local class is
  assumed here. For every `(g, h)` and `k`, the value at `k` of the semilocal
  projection of `f (g, h)` is the `w`-coordinate of `k • f (g, h)`, which is
  a valuation unit. So the semilocal projection of `f` is the image of a
  function into `Coind(U_w)`. That function is a 2-cocycle,
  because the inclusion is injective (the published
  `mem_cocycles₂_of_injective`). Its class is zero by
  `isZero_H2_coindLocalUnits`. The image of a primitive of it is the
  required `β`.

## Injectivity

- `ideleCoordinate_d₁₂_eq`: let `β` be a 1-cochain with values in
  `Coind(E_wˣ)` whose coboundary is the semilocal projection of `f` at
  `w | v`. Let `b` be a 1-cochain of `J_E` such that, for every `k`, `b k`
  has the same coordinates at the places over `v` as the semilocal section of
  `β k`. Then the coboundary of `b` has the same coordinates as `f` at every
  place over `v`. The semilocal section is a morphism of representations, so
  it carries the coboundary of `β` to the coboundary of its composite with
  `β`. The coordinates of `d b` at the places over `v` depend only on those
  of the values of `b`, by `ideleCoordinate_relativeIdeleAut_eq`. The last
  step is `ideleCoordinate_ideleSemilocalSection_ideleSemilocalProjection`.
- `H2π_eq_zero_of_ideleLocalMap_eq_zero`: the main theorem. Its hypotheses
  are: `E / F` Galois; at every pair of finite places `w | v`,
  `H²(Gal(E_w/F_v), E_wˣ)` finite (`hfin`) with at most `[E_w : F_v]`
  elements (`hcard`); a choice of a place `wf v` over each finite place `v`;
  a 2-cocycle `f` of `J_E` whose values all have infinite adele part `1`
  (`hinf`); and `ideleLocalMap v (wf v) 2` killing the class of `f` for every
  finite place `v` (`hloc`). The conclusion is that the class of `f` in
  `H²(Gal(E/F), J_E)` is zero.

  The proof constructs a 1-cochain `b` with `d b = f`. `Gal(E/F)` is finite,
  so `f` has finitely many values. Let `T` be the finite set of places of `E`
  where some value of `f` has a coordinate outside the valuation units,
  together with the ramified places. This is finite by the published
  `finite_setOf_ideleCoordinate_not_mem_localUnits` and
  `finite_setOf_ramificationIdx_ne_one`. For each finite place `v` of `F`,
  choose a primitive `β_v` of the semilocal projection of `f` at `wf v`. If
  no place over `v` lies in `T`, take `β_v` with values in the valuation
  units, by `exists_d₁₂_eq_ideleSemilocalProjection_units`. Otherwise use
  `hloc v` and `exists_d₁₂_eq_ideleSemilocalProjection`. For `g ∈ Gal(E/F)`,
  let `b g` be `ideleOfCoordinates` of the family whose coordinate at `w` is
  the `w`-coordinate of the semilocal section of `β_{placeBelow F w} g`.
  These coordinates are valuation units at every `w` outside the finite set
  of conjugates of places in `T`. There, the values of `β_v` are units, so by
  `ideleSemilocalProjection_ideleSemilocalSection` and
  `ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection` the
  coordinates of the semilocal section at the places over `v` are units. By
  `idele_ext`, it suffices to compare `d b (g, h)` with `f (g, h)` at the
  infinite part and at each finite place. The infinite parts are both `1`,
  since all values of `b` lie in `ideleInfiniteTrivial`, a subgroup stable
  under `Gal(E/F)`, and by `hinf`. At a finite place `w` over `v`, use
  `ideleCoordinate_d₁₂_eq` with `β_v` and `placeBelow_eq`.

## Sources and provenance

Milne, *Class Field Theory* (v4.03, 2020), Chapter VII §2,
Proposition 2.5(b) and its proof, printed pp. 205–206 (PDF pp. 214–215),
proves `Hʳ(G, I_L) = ⊕_v Hʳ(G_v, L_vˣ)` for `r > 0`, where `G_v = G_w` for a
chosen `w | v` (Remark 2.4, printed p. 205, PDF p. 214). He writes `I_L` as the
directed union of the groups `I_{L,S}`, applies Shapiro's lemma to each factor
through Proposition 2.3, and uses the vanishing of `Hʳ(G_v, U_v)` at the
unramified places (Chapter III, Proposition 1.1). The injectivity of the map
to the sum of the local groups is part of that statement.

This module proves the corresponding injectivity in degree `2` for the
finite places, with the cardinality hypothesis inherited from the published
`LocalUnitVanishing`, and only for cocycles with infinite adele part `1`. The
proof works with a single cocycle rather than a direct limit: the finite set
`T` plays the role of `S`, and the primitive is assembled place by place from
the semilocal primitives. The cochain-level gluing, the use of the semilocal
section on all of `J_E`, and the form of the hypotheses (a chosen place over
each `v`, the infinite-part condition) are internal. The helper definitions
`placeBelow`, `ideleOfCoordinates`, `ideleInfiniteTrivial` and
`coindLocalUnitsInclusion` are internal constructions used by the proof.
