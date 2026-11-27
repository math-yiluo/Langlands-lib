# Torus regression examples for KP building data

This module states five propositions about tori and the Kaletha–Prasad building data of the
Library, and their conjunction `KPTorusRegressionStatement`. It proves nothing. The
propositions test that the Library keeps apart

- the reduced building `B(T)` and the enlarged building `B(T) × CentralFactor T`;
- the Iwahori subgroup `T(F)^0`, the maximal bounded subgroup `T(F)^1` and the full group
  `T(F)` (the full stabilizer of every point of `B(T)`);

and they record the component data `T(F)/T(F)^0` and the finite reductive quotient for split
tori and for norm-one tori of quadratic extensions, in every residue characteristic.

## Sources

- T. Kaletha and G. Prasad, *Bruhat–Tits theory: a new approach*, Cambridge University Press
  (2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Printed page `p` is
  PDF page `p + 31`. Cited below as KP.
- T. Kaletha and G. Prasad, *Corrections and additions to Bruhat–Tits theory: a new approach*
  (version of 1 November 2024), registered as `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. Its replacement of KP
  Remark 2.5.15 (PDF pp. 24–25) computes the norm-one torus of a separable quadratic
  extension. It has no correction to §4.3 or §11.1.

The KP results used are: Lemma 2.5.7 (the valuation homomorphism of a split torus is onto
`X_*(T)`, printed p. 88); Proposition 2.5.8 (`T(k)^1 = T(k)^b`, the maximal bounded subgroup,
p. 88); Definition 2.5.13 (`T(K)^0` and `T(k)^0 = T(K)^0 ∩ T(k)`, p. 90); Lemma 2.5.14
(`T(k)^0 ⊆ T(k)^1` with finite index, p. 90); Lemma 2.5.18 (induced ramification gives
`T(k)^0 = T(k)^1`, p. 91); Definition 2.6.23 (`G(k)^0`, p. 104); §4.3, Lemma 4.3.1,
Definition 4.3.2 and Lemma 4.3.3 (the enlarged building `B(G) × V(A_G)` and its stabilizers
`G(k)^1_x`, pp. 178–179); §11.1, Propositions 11.1.1 and 11.1.5, Corollary 11.1.6 and
Remark 11.1.7 (the Kottwitz homomorphism of a torus, `T(K)^0 = ker κ_T`, and
`T(k)/T(k)^0 ≅ (X_*(T)_I)^Γ` for finite residue fields, pp. 421–423).

## Common setting

Every statement is universe-polymorphic: `F : Type u` is a nonarchimedean local field of
either characteristic (`IsNonarchimedeanLocalField F`), and `q = Nat.card 𝓀[F]` is the
cardinality of its residue field.

- **The torus.** `T` is a group scheme over `Spec F` with the Library's `IsTorus T` (it splits
  over a field extension of `F`), or `IsSplitTorus T` for split tori. The norm-one torus of
  `E/F` is the Library's `WeilGm.normOne (CommRingCat.of F) E`, the kernel of the norm
  `R_{E/F} 𝔾_m → 𝔾_m`.
- **The affine instance.** `KPBuildingDatum T` needs `[IsAffineHom T.X.hom]`. It is not an extra
  premise: the statements construct it from the torus hypothesis with
  `IsTorus.isRelativeTorus` and `RelativeTorus.IsTorus.isAffineHom` (for split tori from
  `RelativeTorus.IsTorus.of_isSplitTorus`), and for norm-one tori the Library instance
  `WeilGm.normOne_isAffineHom` applies. The instance is a proposition, so any two choices
  agree.
- **The datum.** `D : KPBuildingDatum T` with `D.SatisfiesGroupAxioms`, the clauses of the ten
  axioms of corrected KP Definition 4.1.26 that concern one group. The comparisons between
  groups (KP Axiom 4.1.17 and the comparison part of Axiom 4.1.1) are not assumed; no
  conclusion below uses them. The Library's `groupAxiomsExistence` proves that every connected
  reductive group, so every torus, has such a datum, so the quantification over `D` is not
  vacuous.

The objects are the Library's, used unchanged. Write `B = D.base.toValuationBuildingData`.

- `B.ReducedBuilding`: the reduced building `B(T)`, the quotient (7.6.2) of `T(F) × A(S)` of
  KP Remark 7.6.5.
- `CentralFactor T = (rationalCharacters T →+ ℝ)`, the real dual of the group `X^*_F(T)` of
  `F`-rational characters, and `B.EnlargedBuilding = B.ReducedBuilding × CentralFactor T`
  with the diagonal action. `CentralFactor T` plays the role of KP's
  `V(A_T) = ℝ ⊗ X_*(A_T)`: KP §4.3 identifies `V(A_G)` with `ℝ ⊗ X_*(G_ab)^Θ`, which is paired
  with the rational characters `X^*(G_ab)^Θ` and is their real dual; for a torus `G_ab = T`.
  The action of `t ∈ T(F)` is translation by the negative of the valuation homomorphism, the
  rule `⟨tλ, χ⟩ = ⟨λ, χ⟩ − ω(χ(t))` of KP §4.3.
- `BuildingFacet B`: the facets of `B(T)`, from `Langlands.BruhatTits.IntegralModels`.
- `T(F)^0` is written `D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j)`.
  `D.base.centralizerZero` is the Library's `Z(F)^0 = Z(K)^0 ∩ Z(F)` of KP Definition
  2.6.23(2) for the centralizer `j : Z → T` of the maximal split torus, with `Z(K)^0` the
  norm image of KP Definition 2.5.13. For a torus `Z = T`, and the map along `j` places the
  subgroup in `T(F)`. No new name is introduced for it.
- `T(F)^1` is `rationalCommonNormKernel T`, the elements on which every rational character has
  absolute value one: the maximal bounded subgroup of KP Proposition 2.5.8.
- `B.fixer y` is the full stabilizer of `y ∈ B(T)`, `B.compactStabilizer y` is
  `T(F)^1 ⊓ B.fixer y` (KP's `G(k)^1_x`), and `B.enlargedStabilizer z` is the stabilizer of a
  point of the enlarged building.
- `D.parahoric x`, `D.finiteReductiveQuotientGroup x hD`: the integral points of the neutral
  facet model at the facet `x`, and the residue-field points of its specified reductive
  quotient, from `Langlands.Geometry.Building.DepthZero.Definitions`.

`T(F)^0`, `T(F)^1` and `T(F)` remain three different Library objects; each relation between
them below is a conclusion.

## The statements

### `KPTorusBuildingStatement` (every torus)

For a torus `T`:

1. `CentralFactor T` is finite-dimensional and `finrank ℝ (CentralFactor T) = splitRank T`
   (as elements of `ℕ∞`). `X^*_F(T)` is free of rank equal to the `F`-split rank.

For every datum `D` with `D.SatisfiesGroupAxioms`:

2. `B(T)` has exactly one point. A torus has no relative roots, so the translation space
   `V(S)/V(S)^Φ` of the apartment is zero and the apartment is one point; `T(F)` acts trivially
   on it, so the quotient (7.6.2) is one point.
3. The enlarged building has exactly one point if and only if `T` is anisotropic
   (`IsAnisotropic T`, split rank zero). By 2 the enlarged building is `CentralFactor T`
   up to a point, and by 1 that is a point exactly when the split rank is zero.
4. There is exactly one facet.
5. `T(F)^0 ≤ T(F)^1` (KP Lemma 2.5.14).
6. At the facet `x`, `D.parahoric x = T(F)^0`. Axiom 4.1.20 in the Library
   (`BuildingModelFamily.ModelAxiomClauses.neutral_points`) makes the neutral integral points
   the pointwise fixer intersected with `G(F)^0 = G(F)^♮ ⊔ Z(F)^0` (KP Definition 2.6.23(3)).
   For a torus the pointwise fixer is `T(F)` and `G(F)^♮`, the image of the simply connected
   cover of the trivial derived group, is trivial.
7. At every point `y`, `B.compactStabilizer y = T(F)^1` and `B.fixer y = ⊤`.
8. Every point of the enlarged building has stabilizer `T(F)^1` (KP Lemmas 4.3.1 and 4.3.3).

Together with the next statements this shows that `T(F)^0`, `T(F)^1` and `T(F)` differ in
general: `T(F)^1 ≠ T(F)` for split tori of positive rank and `T(F)^0 ≠ T(F)^1` for the
ramified norm-one torus.

### `KPSplitTorusBuildingStatement` (split tori)

For a split torus `T` with `splitRank T = N` and every `D` with `D.SatisfiesGroupAxioms`:

1. `T(F)^0 = T(F)^1`: a split torus is induced, so this is KP Lemma 2.5.18. Directly,
   `T(F)^0 = T(F)^1 = (𝒪_F^×)^N` in coordinates `T ≅ 𝔾_m^N`.
2. `T(F)^0` is normal, and there are an additive isomorphism
   `e : Hom(X^*_F(T), ℤ) ≃ ℤ^N` and a group isomorphism `φ : T(F)/T(F)^0 ≃ ℤ^N` with
   `φ(t T(F)^0) = e(val(t))` for every `t`, where `val = rationalCharacterValuation T`
   sends `t` to `χ ↦ ord_F(χ(t))`. So the valuation homomorphism has kernel `T(F)^0` and is
   onto (KP Lemma 2.5.7), and the component group is free of rank `N`. Normality is part of
   the conclusion because the Library's `rationalPoints T` is a group, not a commutative group.
   The isomorphism `e` is existential; any choice of basis of `X^*_F(T)` gives one.
3. At every facet `x`, the finite reductive quotient has `(q - 1)^N` elements. Axiom 4.1.20(3)
   (the integral split torus of the facet model is a closed subgroup with maximal split
   special fibre) forces the neutral model to be the split `𝒪_F`-torus `𝔾_m^N`, whose special
   fibre `𝔾_m^N` is its own maximal reductive quotient with `(q - 1)^N` points over `𝓀[F]`.
   This count is derived from the axioms, not quoted from KP.

### `KPAnisotropicTorusStatement` (anisotropic tori)

For a torus `T` with `IsAnisotropic T`:

1. `T(F)^1 = T(F)`: there are no nontrivial `F`-rational characters.
2. `T(F)` is compact in the canonical topology `rationalPointTopology F T.X` on `F`-points:
   by 1 and KP Proposition 2.5.8 it is bounded, and it is closed, so it is compact because `F`
   is locally compact.
3. For every `D` with `D.SatisfiesGroupAxioms`, every point of the enlarged building is fixed
   by all of `T(F)`.

The norm-one tori below are anisotropic, so they are instances of this statement.

### `KPUnramifiedNormOneTorusStatement` (unramified quadratic extensions)

`E` is an intermediate field of `SeparableClosure F` over `F` with `finrank F E = 2`, so a
separable quadratic extension, and `LocalGalois.Separable.ArithmeticUnramified F E`: the
maximal ideal of `𝒪_F` generates that of `𝒪_E` and the residue extension is separable. For
`T = R¹_{E/F} 𝔾_m` and every `D` with `D.SatisfiesGroupAxioms`:

1. `T(F)^0 = T(F)` (the corrected KP Remark 2.5.15: equality in the unramified case).
2. At every facet the finite reductive quotient has `q + 1` elements. Here the neutral model is
   the norm-one torus of `𝒪_E/𝒪_F`, whose special fibre is the norm-one torus of the residue
   extension `𝔽_{q^2}/𝔽_q`, with `(q^2 - 1)/(q - 1) = q + 1` points. This count is derived, not
   quoted from KP.

### `KPRamifiedNormOneTorusStatement` (ramified quadratic extensions)

`E` as above with `¬ LocalGalois.Separable.ArithmeticUnramified F E`. Residue fields of local
fields are finite, so the residue extension is always separable and the hypothesis says that
the ramification index is `2`. No hypothesis is made on the residue characteristic, so
residue characteristic `2` (wild ramification) is included. For `T = R¹_{E/F} 𝔾_m` and every
`D` with `D.SatisfiesGroupAxioms`:

1. `T(F)^1 = T(F)`.
2. `T(F)^0` has index `2` in `T(F)`. Mathlib's `Subgroup.index` is `0` for infinite index, so
   this asserts a finite index equal to `2`. The corrected KP Remark 2.5.15 computes
   `T(F)^0 = 𝒪_E^×/𝒪_F^× ⊂ E^×/F^× = T(F)`, of index 2. Independently, by §11.1,
   `X_*(T) = ℤ` with inertia acting by `−1`, so `X_*(T)_I = ℤ/2`, and Corollary 11.1.6 with
   Remark 11.1.7 gives `[T(F) : T(F)^0] = 2` in every residue characteristic.

This is the example with nontrivial component data: `T(F)^0 ⊊ T(F)^1 = T(F)`.

### `KPTorusRegressionStatement`

The conjunction of the five statements above, at one universe level.

## Scope

- The quantification is over every datum satisfying the one-group axioms; the statements do
  not choose a datum.
- The module `Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero` treats the norm-one
  torus with a supplied integral form; the statements here concern the building data
  `KPBuildingDatum` instead, and use that module only for the instance
  `WeilGm.normOne_isAffineHom`.
- Nothing is asserted about the topology of the building or the enlarged building.
