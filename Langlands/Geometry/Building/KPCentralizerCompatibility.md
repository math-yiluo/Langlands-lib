# Axiom V 6 on the actual centralizer `Z(k)`

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects. It continues the
modules `KPApartment` and `KPBuilding`. `KPApartmentData` imposes only the part
of axiom V 6 that concerns `S(k)`. This module states the full axiom V 6 on the
actual centralizer `Z(k) = Z_G(S)(k)`. From it we derive the translation action
of `Z(k)` on the apartment and the inclusion `Z(k)^1 ⊆ K_x` for points `x` of
the apartment.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Notation 2.6.15, the valuation homomorphism `ω_G` (2.6.3) and `G(k)^1`, and
  Lemma 2.6.16, printed pp. 102–103, PDF pp. 133–134.
- Axiom 4.1.4 (A 1), the translation `ν(z) = -ω_Z(z)`, and Remark 4.1.5 on its
  sign, printed p. 159, PDF p. 190.
- Definition 6.1.2, axiom V 6, printed p. 199, PDF p. 230.
- Propositions 6.2.3 and 6.2.4, printed pp. 214–215, PDF pp. 245–246.

The corrections of 1 November 2024 (`kaletha-prasad-2024-corrections`) were
checked. On PDF p. 25 they change the fourth line of §2.6(d): `ω_G` is
`g ↦ (χ ↦ ω(χ(g)))`, without the minus sign of the printed (2.6.3). We use the
corrected sign. Then `ν(z) = -ω_Z(z)` gives `a(ν(s)) = -ω(a(s))` for
`s ∈ S(k)`, as KP note after Axiom 4.1.4 (A 1) and in V 6. None of the other
corrections changes Axiom 4.1.4, Definition 6.1.2 or Propositions 6.2.3–6.2.4.

## Setting

`F` is a nonarchimedean local field (`[ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), and `i : S.toGrp ⟶ G` is as in
`KPApartment`. The centralizer enters through a group scheme `Z`, a
homomorphism `j : Z ⟶ G` and a factorization `s : S.toGrp ⟶ Z` of `i`. KP's
`Z(k)` is `rationalPoints Z`, acting on `G(k)` through `rationalPoints.map j`.

`ω_Z` is the published `Cartan.centralizerValuation s h`. It is defined when
`h : Function.Bijective (Cartan.restrictionEvaluation s)`, that is, when
restricting rational characters of `Z` to `S` and evaluating them identifies
`V(S)` with the real dual of `X^*(Z)`. It is characterized by
`χ|_S(ω_Z(z)) = ω(χ(z))` for every rational character `χ` of `Z`
(`Cartan.centralizerValuation_spec`). This is the corrected positive
normalization above, read through that identification of `V(S)`. The published
statement target `Cartan.CentralizerValuationComparisonStatement` asserts the
bijectivity when `G` is connected reductive, `i` is a maximal split torus, `j`
is a closed subgroup representing the torus centralizer and `s ≫ j = i`. It is
not proved, so `h` is an explicit hypothesis everywhere.

## The translation `ν`

- `centralizerTranslation s h : rationalPoints Z →* Multiplicative (V S)` is
  `ν = -ω_Z`, the pointwise inverse of `Cartan.centralizerValuation s h`
  (Axiom 4.1.4 (A 1)). `centralizerTranslation_toAdd` unfolds it.
- `eval_centralizerTranslation`: `χ|_S(ν(z)) = -ω(χ(z))`.
- `centralizerTranslation_ker`: the kernel of `ν` is
  `rationalCommonNormKernel Z`, that is `Z(k)^1` (Lemma 2.6.16(4)). It follows
  from the published `Cartan.centralizerValuation_ker`.

KP define `ν(z)` as the image of `-ω_Z(z)` in `V(S')`. Here `ν` takes values in
`V(S)`, and the image in the apartment's translation space
`TranslationSpace i = V(S)/rootAnnihilator` is taken where `ν` acts on the
apartment. Pairings `a(ν(z))` with roots are the same in both versions.

## Axiom V 6

- `IsCentralizerCompatible i j s h φ` is V 6 of Definition 6.1.2 for a family
  `φ`: for every relative root `a`, `z ∈ Z(k)` and `u ∈ U_a(k)`,
  `φ_a(j(z)⁻¹ u j(z)) = φ_a(u) + a(ν(z))`.
- `IsCentralizerCompatible.vadd`: translates `φ + v` of a V 6-compatible
  family are V 6-compatible, since `(φ + v)_a = φ_a + a(v)`.

For valid apartment data `D : KPApartmentData i (localFieldOrder F)`:

- `D.IsCentralizerCompatible j s h` says that every valuation in the class `A`
  satisfies V 6. This is KP's standing hypothesis that `A` consists of
  `ω`-compatible valuations (Definition 6.1.2 and Proposition 6.2.4).
- `isCentralizerCompatible_iff_of_mem`: it is enough to check one valuation of
  `A`, because the others are its translates.
- `Apartment.isCentralizerCompatible` reads V 6 off a point of the apartment.

## `Z(k)` inside `N(k)` and its action

Assume `hj : (torusCentralizer i).IsRepresentedBy j`, i.e. `j` represents the
actual torus centralizer functor.

- `map_mem_centralizerPoints`: `j(z)` centralizes `i`.
- `centralizerToNormalizer i j hj : rationalPoints Z →* normalizerPoints i` is
  the resulting homomorphism `Z(k) → N(k)`, with `coe_centralizerToNormalizer`.
- `weylAction_centralizerToNormalizer`: `j(z)` acts trivially on `X^*(S)`.
- `IsCentralizerCompatible.smul_eq_vadd`: for a valuation `φ` satisfying V 6,
  `z · φ = φ + ν(z)`. This is the last claim of Proposition 6.2.4, with
  `μ = ν` by Proposition 6.2.3. The proof uses the published formula
  `(nφ)_a(g) = φ_{n⁻¹·a}(n⁻¹ g n)` with trivial Weyl action. Off `U_a(k)` both
  sides are `⊤`, since `j(z)` normalizes `U_a(k)` (`conj_mem_rootGroupPoints`
  from `KPBuilding`).
- `map_mem_rationalCommonNormKernel`: `j` maps `Z(k)^1` into `G(k)^1`
  (Lemma 2.6.16(2) for this homomorphism; the proof restricts characters along
  `j`).

For `D` satisfying `D.IsCentralizerCompatible j s h`:

- `KPApartmentData.centralizerToNormalizer_smul`: `z · x = x + [ν(z)]` for
  `x ∈ A`, where `[ν(z)]` is the class in `TranslationSpace i` (Axiom 4.1.4
  (A 1), Proposition 6.2.4).
- `KPApartmentData.centralizerToNormalizer_smul_eq_self`: `Z(k)^1` acts
  trivially on `A`.
- `KPApartmentData.map_mem_compactStabilizer`: `j(Z(k)^1) ⊆ K_x` for every
  `x ∈ A`, where `K_x = D.compactStabilizer (D.apartmentMap x)` is the
  compact stabilizer of `KPBuilding`. The element lies in `G(k)^1` by
  `map_mem_rationalCommonNormKernel`, and it fixes `[1, x]` by the previous
  item and the `N(k)`-equivariance of `apartmentMap`.

## The bundled actual centralizer

`CentralizerDatum i` bundles the centralizer data used above:

- `Z`, `j : Z ⟶ G` and `s : S.toGrp ⟶ Z`;
- `isClosedSubgroup : IsClosedSubgroup j`;
- `isRepresentedBy : (torusCentralizer i).IsRepresentedBy j`;
- `comp_eq : s ≫ j = i`;
- `bijective : Function.Bijective (Cartan.restrictionEvaluation s)`.

The first four conditions are the hypotheses of
`Cartan.CentralizerValuationComparisonStatement`, and `bijective` is its
conclusion. So for connected reductive `G` and a maximal split torus `i`, a
datum exists as soon as that statement is proved and a represented closed
centralizer is given. Neither is supplied here. `isClosedSubgroup` and
`comp_eq` are not used in the proofs. They make `Z` the actual centralizer
subgroup and `s` the inclusion of `S` into it.

- `C.translation` is `ν` for the datum, and `C.toNormalizer` is
  `Z(k) → N(k)`.
- `D.IsOmegaCompatible C` is `D.IsCentralizerCompatible C.j C.s C.bijective`:
  the data `D` are `ω`-compatible in the sense of Definition 6.1.2.
- `IsOmegaCompatible.smul_eq_vadd`, `IsOmegaCompatible.smul_eq_self` and
  `IsOmegaCompatible.map_mem_compactStabilizer` restate the three results of
  the previous section for the datum.

## What is not proved or defined

- That V 6 implies the `S(k)`-part `IsSplitTorusCompatible` stored in
  `KPApartmentData`. With `comp_eq` this reduces to comparing `ν` on `s(S(k))`
  with the split-torus valuation of `S`, including the comparison of
  `localFieldOrder F` with the normalization of `rationalCharacterValuation`.
  It is not done here.
- The bijectivity of `Cartan.restrictionEvaluation s`, i.e.
  `Cartan.CentralizerValuationComparisonStatement`.
- KP's assertion that the maximal bounded subgroup `Z(k)_b` and the centre act
  trivially. We prove it for `Z(k)^1`. The equality `Z(k)^1 = Z(k)_b` for the
  centralizer of a maximal split torus is not proved.
- The kernel statement of Proposition 6.2.4 (the kernel of the action of
  `N(k) ∩ G(k)^1` on `A` is `Z(k)^1`), the existence part of
  Proposition 6.2.3 (a `μ` for every valuation, without V 6), and axiom V 7.
- `Z(k)^0`, `G(k)^0` and the parahoric subgroups `P_x = Z(k)^0 · G(k)^♯_x` of
  KP Definition 7.4.1(4) are not defined here. They need the Iwahori subgroup
  of `Z(k)` and `G(k)^0` (KP Definition 2.6.23). The later modules
  `KPZeroSubgroups` and `KPParahoric` of the same task define them, for the
  centralizer of a `CentralizerDatum`, on `ParahoricBuildingData G`.
