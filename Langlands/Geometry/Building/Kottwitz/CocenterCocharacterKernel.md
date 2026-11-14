# Cocharacters of a maximal torus mapped to the actual cocenter

This module is internal supporting content for the proof of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Lemma 11.5.2, printed p. 431,
PDF p. 462. That proof presents `π₁(G) = X_*(T)/X_*(T_sc)` and uses that the
map to `X_*(T)/X_*(T_der) = X_*(G_ab)` is surjective with finite kernel. The
module proves the geometric input of that step for the actual objects of the
Library: the maximal torus `T` of a `Choice k G`, its full preimage torus `T_sc`
in the simply connected cover, and an actual `Cocenter k G`, that is, a torus
`D` with an fppf quotient `q : G → D` by the full derived subgroup. Over the
separable closure, the cocharacter map `X_*(T) → X_*(D)` is surjective, and every
cocharacter it kills has a positive multiple in the image of `X_*(T_sc)`. It does
not state finiteness of the kernel, and it does not mention inertia coinvariants;
those steps are in `CocenterTargetTorsionReduction`.

## The torus `T ∩ G_der`

In the namespace `AlgebraicFundamentalGroup.Choice`, for a choice `a`:

- `derivedTorus_isTorus` states that the full scheme-theoretic intersection
  `subgroupIntersection a.inclusion a.derivedInclusion` of the maximal torus and
  the derived subgroup representative is a torus. It is the published
  `derivedMaximalTorusIntersection`, applied to the reductivity, derived-subgroup
  and maximality data stored in `a`.
- `derivedTorus` is this intersection, as a commutative group scheme, and
  `derivedTorusInclusion` is its first projection to `T`.
- `scToDerivedTorus : T_sc → T ∩ G_der` is the actual homomorphism given by the
  pullback property of `T ∩ G_der`. Its first leg is the projection of `T_sc` to
  `T`, and its second leg is `T_sc → G_sc → G_der`. The lemma
  `scToDerivedTorus_comp_inclusion` says that its composite with
  `derivedTorusInclusion` is `a.scToTorus`, and `scToDerivedTorus_comp_snd` says
  that its composite with the projection to `G_der` is `T_sc → G_sc → G_der`.
- `scToDerivedTorus_isPullback` proves that the square formed by
  `T_sc → G_sc`, `scToDerivedTorus`, the central cover `G_sc → G_der` and the
  projection `T ∩ G_der → G_der` is a pullback. Here `T_sc` is by definition the
  pullback of `T → G` along `G_sc → G_der → G`, and the pasting lemma
  `IsPullback.of_bot` cancels the pullback square defining `T ∩ G_der`.
- `flat_scToDerivedTorus` and `surjective_scToDerivedTorus` then follow from the
  flatness and surjectivity of the central isogeny `G_sc → G_der`, because both
  properties are stable under base change.

## The cocharacter map to the cocenter

In the namespace `Geometry.Building.Kottwitz`, for a cocenter `c` and a choice
`a`:

- `Cocenter.torusMap c a : T → D` is the actual homomorphism
  `a.inclusion ≫ c.quotient`.
- `Cocenter.torusCocharacterMap c a E`, for every field extension `E/k` in the
  same universe, is the integral linear map `geometricCocharacterMap k E` of
  `Cocenter.torusMap c a`, from `a.lattice E` to the geometric cocharacters of
  `D`. The lemma `Cocenter.torusCocharacterMap_apply` records that it sends a
  cocharacter `ν` to `ν` followed by the base change of `T → D` to `E`.

`Cocenter.exists_pos_smul_mem_corootImage` takes `E = SeparableClosure k`. If
`Cocenter.torusCocharacterMap c a E ν = 0`, it gives an integer `n > 0` with
`n • ν ∈ a.corootImage E`, the image of `X_*(T_sc) → X_*(T)` over `E`. The proof
runs as follows.

1. The derived subgroup of `G_E` is the base change of the derived subgroup of
   `G` (`derivedSubgroup_baseChange_eq_of_field`). So the base change of `q` is
   again an fppf quotient by the derived subgroup, and the base change of the
   derived representative still represents it.
2. The composite `𝔾_m → T_E → G_E` of `ν` with the inclusion is killed by
   `q_E`. By the full-kernel clause of the quotient, its range lies in the
   derived subgroup of `G_E`, so it lifts to the derived representative over
   `E`. The base-changed pullback square of `T ∩ G_der` then gives a
   cocharacter `ν'` of `(T ∩ G_der)_E` whose image in `T_E` is `ν`.
3. The tori `T_sc` and `T ∩ G_der` split over the separable closure
   (`GaloisPinningData.isSplitTorus_separableClosure`), and the base change of
   `scToDerivedTorus` to `E` is flat and surjective. The published
   `IsSplitTorus.exists_positive_multiple_cocharacter_lift_of_flat_surjective`
   gives `n > 0` and a cocharacter `ξ` of `T_sc,E` mapping to `n • ν'`.
4. Composing with `derivedTorusInclusion` and using
   `scToDerivedTorus_comp_inclusion`, the image of `ξ` under `a.scToTorus` is
   `n • ν`.

`Cocenter.torusCocharacterMap_surjective` proves that the map
`Cocenter.torusCocharacterMap c a (SeparableClosure k)` is surjective. The
published `cocenterQuotientExistence` gives a cocenter quotient `q₀ : G → Q₀`
whose cocharacter map from every maximal torus is surjective over every field
that splits the torus. The maximal torus `T` splits over the separable closure.
Both `q₀` and `c.quotient` are fppf quotients by the range of the derived
representative, so `FppfQuotientComparison.iso` gives an isomorphism
`e : Q₀ ≅ D` with `q₀ ≫ e = c.quotient`. Thus `T → D` factors as `T → Q₀`
followed by `e`. A cocharacter `ν'` of `D_E` is lifted by lifting
`ν' ≫ e⁻¹_E` along `T → Q₀`.

## Provenance

These are internal definitions and derived lemmas. The definitions are the
evident composites `T → G → D` and `T_sc → T ∩ G_der` of actual Library
morphisms, and the lemmas implement for these objects the surjection with
finite kernel used in the proof of KP Lemma 11.5.2. Here `T ∩ G_der` is the
scheme-theoretic intersection supplied by `subgroupIntersection`. In place of
the finite kernel, the module proves only that the kernel is torsion modulo the
coroot image. No hypothesis on the cocenter beyond the `Cocenter` structure, and
no splitting or simple-connectedness assumption on `G`, is added.

`Cocenter.torusMap c a` reuses [cocenterTorusRestriction](CocenterTorusRestriction.md) with reversed argument order.
