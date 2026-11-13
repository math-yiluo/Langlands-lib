# The standard and the dynamic constant terms of Proposition I.6.2 agree

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Jacquet.StandardDynamicConstantTerm`, namespace
`Langlands.Jacquet`.

The Library has two published actual forms of Waldspurger's Proposition I.6.2, both by this
author:

- the **standard form** `Langlands.Representation.Jacquet.StandardCasselmanConstantTerm`
  (`IsStandardConstantTerm`, `HasStandardConstantTerm`, `standardConstantTerm`), on the actual
  standard parabolic `P_J = M_J U_J` and the source's cones
  `{a ∈ A(F) ; |α(a)|_F < ε for α ∈ Δ(P_J)}` of a compatible split component `A` of `M_J`;
- the **dynamic form** `Langlands.Representation.Jacquet.DynamicCasselmanConstantTerm`
  (`IsDynamicConstantTerm`, `HasDynamicConstantTerm`, `dynamicConstantTerm`), on the dynamic
  parabolic `P(χ) = Z(χ) U(χ)` of a cocharacter `χ : 𝔾_m → G` and the tails
  `{χ(t)^r ; r ≥ r₀}` of the powers of `χ(t)`, for a unit `t` with `t^n → 0`.

The published standard module lists the comparison of the two as not formalized. This module
proves it. Let `ζ` be a standard cocharacter of `J`. Then `P_J` is the dynamic parabolic of
`ζ ∘ i`, and for every function `f` with a right-finite standard constant term (for example every
`f ∈ A(ρ)`, given the structural data of the standard module) the two constant terms agree:

`dynamicConstantTerm (ζ ∘ i) t f = standardConstantTerm hA f` on `Z(ζ ∘ i)(F) = M_J(F)`,

for every `t` with `t^n → 0`. Therefore, for such `f`, the dynamic constant term depends neither
on `t` nor on the standard cocharacter `ζ`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
numbers; the PDF page is the printed page minus 234. The author checked the quotation below on the
rendered PDF pages 15 and 16.

- Proposition I.6.2, printed pp. 249–250: "Soient `f ∈ A(G)` et `P = MU` un sous-groupe
  parabolique semi-standard de `G`. Il existe un unique élément `f_P ∈ A(M)` vérifiant la
  propriété suivante: pour tout `m ∈ M`, il existe `ε > 0` tel que pour tout `a ∈ A_M` vérifiant
  `|α(a)|_F < ε` pour tout `α ∈ Σ(P)`, on ait l'égalité `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`."

The source states only the cone form. The dynamic form and the description of `P_J` as a
dynamic parabolic are not in the source. They come from the published Library modules named
below, and the comparison proved here is internal to this project. The published
`StandardCasselmanConstantTerm.md` explains the passage between the source's `Σ(P)` cones and the
`Δ(P_J)` cones used in Lean. Both published modules normalize by the Haar modulus `δ_U` on the
radical instead of the source's `δ_P`; see their "Moduli" sections.

## Setting and conventions

`F` is a nonarchimedean local field, and `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`. Its actual points `G(F)` carry the
canonical topology, as in the two published modules. This module uses the local instances of the
standard module (`standardCasselmanTopology`, etc.). The data and hypotheses are those of the
published standard module:

- `i : S → G` is a maximal split torus (`hi : IsMaximalSplitTorus i`);
- `ν` is a generic cocharacter (`hν`);
- `J` is a set of simple relative roots with a standard cocharacter `ζ`
  (`hζ : IsStandardCocharacter i ν J ζ`, i.e. `⟨α, ζ⟩ = 0` for `α ∈ J` and `⟨α, ζ⟩ > 0` for the
  other simple roots);
- `q : A → S` is a compatible split component of `M_J`
  (`hA : IsCompatibleStandardSplitComponent i ν J A q`);
- for the last theorem, also `hG : IsConnectedReductive G`, the basis `B` of `K0`
  (`hB : CompactOpenNormalBasis K0 B`) and `hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K`
  (Renard's V.5.2, unproved inputs, as in the standard module).

Each theorem assumes only the hypotheses it lists. `Δ(P_J)` is
`standardParabolicComponentCharacters i ν J q`, and `|α(y)|_F` is
`CocharacterUniformizer.characterNorm F A α y`. `M_J(F)` and `U_J(F)` are
`standardLeviPoints i ν J` and `standardUnipotentPoints i ν J`. `Z(χ)(F)` and `U(χ)(F)` are
`dynamicLeviPoints χ` and `unipotentPoints χ`. The cocharacter `ζ ∘ i` is written
`CommGroupScheme.groupHom ζ ≫ i` in Lean. `χ(t)` is `cocharPoint χ t`.

## Contents

### Generic lemmas (section `Abstract`)

- `closedRestrictCharacter_congr`: the Library's Haar modulus of conjugation
  `HaarModulus.closedRestrictCharacter U hU M hM m` depends only on the subgroup `U` and on the
  element `m` of `G`. If `U = U'` and `(m : H) = m'`, the two moduli agree, even when `m` and `m'`
  are taken in different normalizing subgroups `M`, `M'`.
- `isRightFinite_comp`: if `φ : M → ℂ` is right finite for `Z` (the Library's `IsRightFinite`)
  and `e : M' →* M` maps `Z'` into `Z`, then `φ ∘ e` is right finite for `Z'`.

### Comparison for a cocharacter with `M_J = Z(χ)`, `U_J = U(χ)` (section `Rational`)

- **`standardLeviDynamicEquiv χ hM`** (definition, the recorded declaration): for
  `hM : standardLevi i ν J = Dynamic.centralizer χ`, the group isomorphism
  `Z(χ)(F) ≃* M_J(F)`, which is the identity on underlying points of `G(F)`
  (`coe_standardLeviDynamicEquiv`). It is `MulEquiv.subgroupCongr` of the equality of the two
  point subgroups.
- `dynamicHalfModulus_eq_standardHalfModulus`: if moreover
  `hU : standardUnipotent i ν J = Dynamic.unipotent χ`, then
  `dynamicHalfModulus χ m = standardHalfModulus i ν J (standardLeviDynamicEquiv χ hM m)`, i.e.
  `δ_{U(χ)}^{1/2} = δ_{U_J}^{1/2}` on `Z(χ)(F) = M_J(F)`.
- `IsStandardConstantTerm.isDynamicConstantTerm`: the cone condition implies the tail condition.
  Assume `hM` and `hU`, that `Δ(P_J)` is finite (`hfin`), and that `χ(t)` is the image of a point
  `y ∈ A(F)` with `|α(y)|_F < 1` for all `α ∈ Δ(P_J)` (`hy`, `hty`). If
  `IsStandardConstantTerm hA f f_P`, then `IsDynamicConstantTerm χ t f (f_P ∘ e)`, where `e` is
  `standardLeviDynamicEquiv χ hM`.
- `HasStandardConstantTerm.dynamicConstantTerm_eq`: under the same hypotheses, if
  `HasStandardConstantTerm hA f`, then `HasDynamicConstantTerm χ t f` and
  `dynamicConstantTerm χ t f = standardConstantTerm hA f ∘ e`.

### Standard cocharacters (section `Standard`)

- `residueNormalizedAbsoluteValue_lt_one_of_tendsto_pow`: if `t^n → 0` in `F`, then `|t|_F < 1`
  (for the Library's normalized absolute value `LocalField.residueNormalizedAbsoluteValue F`).
- `characterNorm_cocharacterPoints`: for a character `α` and a cocharacter `c` of `A`,
  `|α(c(t))|_F = |t|_F^{⟨α, c⟩}`.
- `exists_componentPoint_of_isStandardCocharacter` (`hA`, `hi`, `hζ`): for `t` with `t^n → 0`,
  `ζ(t)` (i.e. `cocharPoint (ζ ∘ i) t`) is the image of a point `y ∈ A(F)` with `|α(y)|_F < 1` for
  every `α ∈ Δ(P_J)`.
- `standardLevi_eq_dynamic` (`hG`, `hi`, `hν`, `hζ`): `standardLevi i ν J` and
  `standardUnipotent i ν J` are the dynamic centralizer and the dynamic unipotent subgroup
  functors of `ζ ∘ i`. This is a projection of the Library's proved `standardCocharacter`.
- **`HasStandardConstantTerm.dynamicConstantTerm_eq_of_isStandardCocharacter`** (`hG`, `hi`,
  `hν`, `hζ`, `hA`): for `t` with `t^n → 0` and `f` with `HasStandardConstantTerm hA f`, `f` has
  a right-finite constant term along the powers of `ζ(t)`, and
  `dynamicConstantTerm (ζ ∘ i) t f` is `standardConstantTerm hA f` transported along
  `standardLeviDynamicEquiv`.
- `HasStandardConstantTerm.dynamicConstantTerm_independent`: take two standard cocharacters
  `ζ, ζ'` of `J` and two units `t, t'` with `t^n → 0` and `t'^n → 0`. For `f` with a right-finite
  standard constant term, `dynamicConstantTerm (ζ ∘ i) t f m` and
  `dynamicConstantTerm (ζ' ∘ i) t' f m'` agree at points `m`, `m'` with the same image in `G(F)`.
- `dynamicConstantTerm_eq_standardConstantTerm` (`hG`, `hi`, `hν`, `hζ`, `hB`, `hA`, `hmem`):
  for an admissible `ρ`, `f ∈ A(ρ)` (`coefficientFunctionSpace`) and `t` with `t^n → 0`, `f` has a
  right-finite constant term along the powers of `ζ(t)`, equal to `standardConstantTerm hA f`
  transported along `standardLeviDynamicEquiv`.

## Proof notes

- *Groups and moduli.* An equality of subgroup functors gives an equality of point subgroups of
  `G(F)` (evaluation at the identity test object `Over.mk (𝟙 _)`), so `MulEquiv.subgroupCongr`
  gives `standardLeviDynamicEquiv`. Both half moduli are square roots of
  `HaarModulus.closedRestrictCharacter` of the radical. The radicals are equal by `hU`, so
  `closedRestrictCharacter_congr` (by `subst`) identifies the two moduli.
- *Cone to tail.* Fix `m`, and let `ε` be the threshold of the standard property at `e(m)`. The
  published `eventually_pow_mem_standardCone` (with `hfin` and `hy`) gives `r₀` such that
  `y^r` lies in the `ε`-cone for `r ≥ r₀`. By `hty`, `e(m χ(t)^r) = e(m) · ȳ^r`, where `ȳ` is the
  image of `y` in `M_J(F)` (`standardComponentHom`). The standard identity at `y^r` is then the
  dynamic identity at `r`, after the moduli are identified.
- *Equality of the constant terms.* `standardConstantTerm hA f` is right finite for the image of
  `A(F)` (`HasStandardConstantTerm.isRightFinite`). Since `e(χ(t)) = ȳ`, `e` maps `⟨χ(t)⟩` into
  that image, and `isRightFinite_comp` makes `standardConstantTerm hA f ∘ e` right finite for
  `⟨χ(t)⟩` (`dynamicCocharSubgroup`). It is a constant term along the powers of `χ(t)`, so the
  Library's `dynamicConstantTerm_eq` identifies it with `dynamicConstantTerm χ t f`.
- *Standard cocharacters.* The published `IsCompatibleStandardSplitComponent.exists_cocharacter_lift`
  gives a cocharacter `c` of `A` with `c ≫ q = ζ`. Take `y = c(t)`. For `α ∈ Δ(P_J)`, the
  restriction of a simple root `β ∉ J`, `⟨α, c⟩ = ⟨β, ζ⟩ > 0`, so
  `|α(y)|_F = |t|_F^{⟨β, ζ⟩} < 1` because `0 < |t|_F < 1`. Finiteness of `Δ(P_J)` comes from the
  published `exists_strictly_contracting_point`. `M_J = Z(ζ ∘ i)` and `U_J = U(ζ ∘ i)` come from
  `standardCocharacter`.
- *`A(ρ)`.* The published `standardConstantTerm_spec` gives `HasStandardConstantTerm hA f` for
  `f ∈ A(ρ)`.

## Relation to the source and scope

- Standard parabolics `P_J` and standard cocharacters `ζ` of `J` only.
- The comparison holds for functions with a right-finite standard constant term. For general `f`
  (for example `f ∈ A(ρ)` without the structural data `hB`, `hmem`), the independence of
  `dynamicConstantTerm` from `t` is not proved. The published dynamic module proves existence for
  every `f ∈ A(ρ)` without structural inputs (`dynamicConstantTerm_spec`, for smooth `G`). The
  standard module needs Renard's V.5.2 data, which are hypotheses (their existence is the
  Library's unproved `JointSpecialCompactBasisExistenceStatement`). This module does not use
  `[Smooth G.X.hom]`.
- Both constant terms are normalized by `δ_U`. This module proves only that the two `δ_U` agree.
  Their identification with Waldspurger's `δ_P` is the unproved comparison described in the
  "Moduli" sections of the two published modules.
- Provenance: internal. All declarations compare two internal Lean forms of Proposition I.6.2
  (printed pp. 249–250) and are derived from the published modules `StandardCasselmanConstantTerm`,
  `DynamicCasselmanConstantTerm`, `JacquetStrictElement` and `StandardCocharacterProof`.
