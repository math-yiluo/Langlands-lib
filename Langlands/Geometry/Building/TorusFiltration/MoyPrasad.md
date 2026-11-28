# The Moy–Prasad homomorphism of KP Proposition B.10.16 for tori

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified
extension, `O = fixedFieldIntegers F` and `𝔪` its maximal ideal. For a `K`-torus `T`
(`hT : IsTorus T.toGrp`) let `T(K)_r = minimalCongruentPoints F T hT r` be the minimal congruent
filtration, `𝒯_r = (minimalCongruentModel F T hT r).val` its constructed smooth models
(`TorusFiltration.Construction`) and `t(K)_r = minimalCongruentLie F T hT r = Lie(𝒯_r)` the
Lie filtration (`TorusFiltration.Lie`).

This module constructs the homomorphism

  `T(K)_r / T(K)_s → t(K)_r / t(K)_s`,   `1 ≤ r ≤ s ≤ r + ⌊r⌋`,

of Kaletha–Prasad, Proposition B.10.16, following its proof: apply the congruence–Lie
homomorphism of KP Proposition A.5.19(3) to the model `𝒯_{r₀}`, `r₀ = r − ⌊r⌋`, at the levels
`n = ⌊r⌋ ≤ 2n`, and pass to the quotients. KP write `r = r₀ + n` with `0 ≤ r₀ < 1` and `n` a
positive integer, so `n = ⌊r⌋`, and allow `r₀ + n ≤ s ≤ r₀ + 2n`, that is `r ≤ s ≤ r + ⌊r⌋`.
This module constructs the map. It does not prove that the map is bijective or functorial.

## Two results taken as arguments

Two results that the Library states in `IntegralModel.CongruenceLieStatements`, and that this
module does not prove, enter as explicit arguments:

- `h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement` (KP Lemma A.5.13(4)): the Lie lattice
  of the level-`k` congruence model of a smooth model `M` is `𝔪^k • Lie(M)`. Through
  `smul_lieLattice_eq_minimalCongruentLie` (`TorusFiltration.Lie`) it gives
  `𝔪^k • t(K)_{r₀} = t(K)_{r₀+k}`.
- `hF : IntegralModel.CongruenceLieFunctorialityStatement` (the functoriality in KP
  Proposition A.5.19(3)): for smooth models `M`, `N` and a model homomorphism `φ : M → N`
  extending `f`, the congruence–Lie homomorphisms commute with the maps that `φ` induces on
  congruence subgroups (`Hom.congruenceSubgroupMap`) and on Lie-lattice quotients
  (`Hom.congruenceLieQuotientMap`).

The homomorphism `minimalCongruentMoyPrasadHom` uses only `h𝔩`; the induced map on the quotient,
`minimalCongruentMoyPrasad`, also uses `hF`, to show that `T(K)_s` lies in the kernel.

## Depths

- `torusMoyPrasadLevel r hr : ℕ+` is `n = ⌊r⌋` for `hr : 1 ≤ r`.
- `torusMoyPrasadBase r : ℝ≥0` is `r₀ = r − ⌊r⌋`.
- `torusMoyPrasadBase_add_level`: `r₀ + n = r`.
- `torusMoyPrasadBase_add_two_mul_level`: `r₀ + 2n = r + ⌊r⌋`.

## The quotients

- `minimalCongruentQuotient F T hT r s` is `T(K)_r ⧸ (T(K)_s ∩ T(K)_r)`, written with
  `Subgroup.subgroupOf`. It is a commutative group because `T` is commutative.
- `minimalCongruentLieQuotient F T hT r s` is the `O`-module `t(K)_r ⧸ (t(K)_s ∩ t(K)_r)`,
  written with `Submodule.comap` along the inclusion `t(K)_r → GenericLie O T.toGrp`.

For `r ≤ s` the intersections are `T(K)_s` and `t(K)_s` (`minimalCongruentPoints_antitone`,
`minimalCongruentLie_antitone`).

## The model `𝒯_{r₀}` at the levels `n` and `2n`

- `congruenceSubgroupAt_torusMoyPrasadLevel`: the level-`n` congruence subgroup of `𝒯_{r₀}` is
  `T(K)_r`, by `congruenceSubgroupAt_eq_minimalCongruentPoints` and `r₀ + n = r`.
- `lieLatticeAt_torusMoyPrasadLevel h𝔩`: its level-`n` Lie lattice `𝔪^n • Lie(𝒯_{r₀})` is
  `t(K)_r`.
- `lieLatticeAt_two_mul_torusMoyPrasadLevel_le h𝔩`: its level-`2n` Lie lattice is
  `t(K)_{r₀+2n} = t(K)_{r+⌊r⌋}`, which lies in `t(K)_s` for `s ≤ r + ⌊r⌋`.

## The construction

- `minimalCongruentMoyPrasadLieMap h𝔩 r s hr hs` is the `O`-linear map from the Lie-lattice
  quotient `Lie_n(𝒯_{r₀}) / Lie_{2n}(𝒯_{r₀})` (`congruenceLieQuotient n (2n)`) to
  `t(K)_r / t(K)_s`. It is the identity on representatives: by the two lattice identities above,
  `Lie_n(𝒯_{r₀}) = t(K)_r` and `Lie_{2n}(𝒯_{r₀}) ⊆ t(K)_s`.
- `minimalCongruentMoyPrasadHom h𝔩 r s hr hs : T(K)_r →* Multiplicative (t(K)_r / t(K)_s)` is
  the composite of
  1. the identification `T(K)_r ≃ (𝒯_{r₀}).congruenceSubgroupAt n`
     (`MulEquiv.subgroupCongr` along `congruenceSubgroupAt_torusMoyPrasadLevel`),
  2. the congruence–Lie homomorphism `(𝒯_{r₀}).congruenceLieHom` at the levels `n ≤ 2n`
     (KP Proposition A.5.19(3)), and
  3. `minimalCongruentMoyPrasadLieMap`.

  `minimalCongruentMoyPrasadHom_apply` gives its value at a point (by `rfl`).
- `minimalCongruentMoyPrasadHom_deeper_le_ker h𝔩 hF r s hr hrs hs`: for `r ≤ s ≤ r + ⌊r⌋`,
  `T(K)_s` lies in the kernel. This is KP's argument "by functoriality". Let
  `s₀ = s − n ≥ r₀`. Since `T(K)_{s₀} ⊆ T(K)_{r₀}`, KP Corollary 2.10.10
  (`IntegralModel.smoothHomExtension` through `exists_hom_of_map_integralPoints_le`) extends
  the identity of `T` to a model homomorphism `φ : 𝒯_{s₀} → 𝒯_{r₀}`. The level-`n` congruence
  subgroup of `𝒯_{s₀}` is `T(K)_s`, and its level-`n` Lie lattice is `t(K)_s`. The differential
  of `φ` is the identity (`GenericLie.map_id`). By `hF`, the image under the congruence–Lie
  homomorphism of `𝒯_{r₀}` of a point of `T(K)_s` is therefore the class of an element of
  `t(K)_s`, which maps to zero in `t(K)_r / t(K)_s`.
- `minimalCongruentMoyPrasad h𝔩 hF r s hr hrs hs` is the induced homomorphism
  `T(K)_r / T(K)_s →* Multiplicative (t(K)_r / t(K)_s)` (`QuotientGroup.lift`). It is the map
  of KP Proposition B.10.16, written multiplicatively on the Lie side.
  `minimalCongruentMoyPrasad_mk` gives its value on the class of a point.

## Maps induced by a homomorphism of tori

For a homomorphism of `K`-tori `f : T ⟶ U`, with `hU : IsTorus U.toGrp`:

- `minimalCongruentPointsMap F hT hU f r : T(K)_r →* U(K)_r` is the restriction of
  `rationalPoints.map (CommGroupScheme.groupHom f)`. It is well defined by the functoriality of
  the filtration (`minimalCongruentFunctoriality`, KP Proposition B.10.10).
- `minimalCongruentQuotientMap F hT hU f r s : T(K)_r / T(K)_s →* U(K)_r / U(K)_s` is the map
  it induces on the quotients.
- `minimalCongruentLieQuotientMap F hT hU f r s : t(K)_r / t(K)_s →ₗ[O] u(K)_r / u(K)_s` is the
  map induced by the differential `GenericLie.map O (CommGroupScheme.groupHom f)`. It is well
  defined by `map_minimalCongruentLie_le`.

These are the maps that the functoriality of KP Proposition B.10.16 compares.

## Implementation notes

- The integer ring `O` is given the local instance `IsDiscreteValuationRing O`, from
  `fixedFieldIntegers_strictHenselian`.
- `IntegralModel.congruenceLieHom`, `minimalCongruentModel` and
  `IntegralModel.Hom.congruenceLieQuotientMap` are made locally irreducible. Otherwise,
  definitional unfolding of these large constructions makes elaboration exceed the heartbeat and
  recursion limits.
- Even so, the private lemma `exists_congruenceLieHom_eq_of_hom`, which applies `hF`, needs a
  limit of 400000 heartbeats, spent on unifying instance arguments over
  `Spec (CommRingCat.of K)`.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page = printed page
+ 31):

- Proposition B.10.16 and its proof (printed p. 694);
- Proposition A.5.19 (printed pp. 641–643);
- Lemma A.5.13(4) (printed pp. 636–637);
- Corollary 2.10.10 (printed p. 124);
- Proposition B.10.10 (printed p. 690).
