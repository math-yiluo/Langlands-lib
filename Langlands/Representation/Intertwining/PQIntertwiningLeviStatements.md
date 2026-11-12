# Renard VII.3.5 (ii)–(iii): intertwining operators and induction in stages

Author: Worker 1222. Module
`Langlands.Representation.Intertwining.PQIntertwiningLeviStatements`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`. The module contains
two **statements**, both `Prop`-valued definitions:

- `PQIntertwiningInnerLeviStatement`: part (ii) of the Proposition of VII.3.5;
- `PQIntertwiningOuterLeviStatement`: part (iii) of the Proposition of VII.3.5.

It proves nothing. Part (i) and the integral normalization of the operators are in
[PQIntegralIntertwiningStatements](PQIntegralIntertwiningStatements.md).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

VII.3.5, printed pp.236–240 / PDF pp.242–246. The Proposition (printed p.237 / PDF p.243)
reads, for a semi-standard Levi subgroup `M`, a smooth representation `(σ, E)` of `M` and
semi-standard parabolics `P₁`, `P₂` with Levi factor `M`:

- (ii) "Si `Q = LU` est un sous-groupe parabolique semi-standard de `G` contenant `P₁` et
  `P₂`, et si `σ` est `P₁P₂`-régulière, alors avec les identifications naturelles et les
  notations évidentes `σ` est `(P₁ ∩ L)(P₂ ∩ L)`-régulière et
  `J^G_{P₂|P₁}(σ) = i^G_Q(J^L_{(P₂∩L)|(P₁∩L)}(σ))`."
- (iii) "Si `L` est un sous-groupe de Levi standard de `G` contenant `M` tel que
  `P₁ ∩ L = P₂ ∩ L` et tel que `Q₁ = P₁L = LU₁`, `Q₂ = P₂L = LU₂` sont des sous-groupes
  paraboliques (de radical unipotent respectivement `U₁` et `U₂`) de `G` et si
  `i^L_{P₁∩L}(σ)` est `(P₁L)(P₂L)`-régulière, alors `σ` est `P₁P₂`-régulière et de plus, avec
  les identifications naturelles et les notations évidentes,
  `J_{P₂|P₁}(σ) = J_{Q₂|Q₁}(i^L_{P₁∩L}(σ))`."

The proof (printed pp.238–240 / PDF pp.244–246) fixes the natural isomorphism
`i^G_{Pᵢ}(E) ≃ i^G_Q ∘ i^L_{Pᵢ∩L}(E)`, `f ↦ f̃`, with
`f̃(g) = f_g : l ∈ L ↦ δ_U(l)^{-1/2} f(lg)`, notes that `i^G_Q(J)(f̃) = J ∘ f̃`, and uses
`(N̄₁ ∩ L) ∩ (N₂ ∩ L) = N̄₁ ∩ N₂` in (ii) and that the inclusion `Ū₁ ∩ U₂ ⊂ N̄₁ ∩ N₂` is a
homeomorphism in (iii), so that the same measure normalizes both operators.

## Published objects used

Everything from [PQIntegralIntertwiningStatements](PQIntegralIntertwiningStatements.md) and
the published VII.3.4 statement, with the meanings described there: `leviInductionFunctor`
(Renard's normalized `i_P^G` on representations of `M(F)`), `Induction.eval`,
`inducingRepresentation`, `leviPointsEquiv`, `pointImage`, `IsSplitComponent`, `IsPQRegular`
(condition (i) of the VII.3.3 Lemma) and `IsIntegralIntertwiner` (the formula
`J(f)(1) = ∫_V f(v) dv`, read against every linear form).

Also used:

- `leviPoints_locallyCompactSpace q lQ hq hlQ` and `leviPoints_nonarchimedeanGroup q lQ hq hlQ`
  (module `Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints`): `L(F)`, with its
  canonical topology, is locally compact and a nonarchimedean group. With these instances and
  `hlQ.isConnectedReductive.isAffineHom`, the represented-parabolic interface (induction,
  regularity, integral normalization) applies with `L` as ambient group;
- `HaarModulus.closedHalfCharacter U hU P hPU`: the positive square root of the Haar modulus of
  conjugation by `P` on the closed subgroup `U`, as a complex character. With `U = U(F)` and
  `P = Q(F)` this is the character `δ_Q^{1/2}` of the published normalized induction `i_Q^G`;
  restricted to `L(F)` it is Renard's `δ_U^{1/2}`. It is evaluated at
  `Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)`, the image of
  `x ∈ L(F)` in `Q(F)`;
- `isSemidirectDecomposition_pointImage … |>.le_normalizer` (the point image of `Q` normalizes
  that of `U`) and `isClosed_pointImage_comp` (the point image of `U` is closed).

From Mathlib: `MeasureTheory.Measure`, `Measure.IsHaarMeasure`, `BorelSpace`, the Bochner
integral, `Continuous`, `HasCompactSupport`, `Subgroup.inclusion`.

## Common conventions

The ambient setting (nonarchimedean local field `k`, connected reductive `G`, canonical topology
on `G(F)`, local compactness and nonarchimedean group structure) and the encoding of
represented parabolics `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`), of opposite
parabolics (same embedded Levi, `P(F) ∩ P̄(F) = M(F)`) and of the integral normalization are
those of [PQIntegralIntertwiningStatements](PQIntegralIntertwiningStatements.md).

**Parabolics of `L`.** A parabolic of `L` with Levi `M` is a represented parabolic
`p' : P' ⟶ L`, `l' : M ⟶ P'`, `r' : N' ⟶ P'` of the group scheme `L`. Renard's `P ∩ L` is
encoded by: the embedding of `M` through `P'`, `L` and `Q` is that of `M` through `P`
(`l' ≫ p' ≫ lQ ≫ q = l₁ ≫ p₁`), and `P'(F)` is `P(F) ∩ L(F)` in `G(F)`
(`pointImage (p' ≫ lQ ≫ q) = pointImage p ⊓ pointImage (lQ ≫ q)`). Inclusions of parabolics
are inclusions of point images (`pointImage p₁ ≤ pointImage q`).

**The natural identification.** `emb = rationalPoints.map (lQ ≫ q) : L(F) → G(F)` and
`c(x) = δ_U(x)^{1/2}` as above. For `f ∈ i_P^G(σ)` and `F ∈ i_Q^G(i_{P'}^L(σ))`, "`F` is `f̃`"
is the condition `F(g)(x) = c(x)⁻¹ f(emb(x) g)` for all `g ∈ G(F)`, `x ∈ L(F)`, where `F(g)`
is evaluated in the induced model of `Q` and `F(g)(x)` in that of `P'`. This is Renard's
formula `f̃(g)(l) = δ_U(l)^{-1/2} f(lg)`, and it is the formula of the Library's construction
`NestedInduction.equiv` (`(equiv A f)(x)(l) = c(l)⁻¹ • f(l x)`). Since `f(g) = f̃(g)(1)`,
the condition determines `f` from `F`. The statements assert that `f̃` exists for every `f`;
Renard's further claim that `f ↦ f̃` is bijective is not needed and not stated.

**`i_Q^G` of an operator.** Renard notes `i^G_Q(J)(f̃) = J ∘ f̃`: the published normalized
induction acts on morphisms by postcomposition. So `i^G_Q(J') (f̃) = (J f)~` is written
`J'(f̃(g))(x) = c(x)⁻¹ (J f)(emb(x) g)` for all `g`, `x`.

## `PQIntertwiningInnerLeviStatement` (VII.3.5 (ii))

Binders: represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` with `l₂ ≫ p₂ = l₁ ≫ p₁`;
`P̄₁ = MN̄₁` opposite to `P₁`; `Q = LU` with `P₁(F), P₂(F) ⊂ Q(F)`; represented parabolics
`P₁' = MN₁'`, `P₂' = MN₂'` of `L` with `l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁`,
`l₂' ≫ p₂' = l₁' ≫ p₁'` and `Pᵢ'(F) = Pᵢ(F) ∩ L(F)`; `P̄₁' = MN̄₁'` opposite to `P₁'` in `L`;
the split component `a : A → M`; `V = N̄₁(F) ∩ N₂(F) ⊂ G(F)` and
`V' = N̄₁'(F) ∩ N₂'(F) ⊂ L(F)` with Borel measurable structures.

Measures `haar'` on `V'` and `haar` on `V` are *compatible* when
`∫_{V'} φ(emb x) dhaar'(x) = ∫_V φ(x) dhaar(x)` for every continuous compactly supported
`φ : G(F) → ℂ`, that is, `haar` is the image of `haar'` under `emb`. This is Renard's
`(N̄₁ ∩ L) ∩ (N₂ ∩ L) = N̄₁ ∩ N₂` read on measures: `N̄₁ ∩ L` is the unipotent radical of the
parabolic `P̄₁ ∩ L` of `L` opposite to `P₁ ∩ L`.

The statement asserts:

1. for every Haar measure `haar'` on `V'` there is a compatible Haar measure `haar` on `V`;
2. for every smooth representation `σ` of `M(F)`:
   - every `f ∈ i_{P₁}^G(σ)` has an `f̃ ∈ i_Q^G(i_{P₁'}^L(σ))`;
   - if `σ` is `P₁P₂`-regular, then `σ` is `P₁'P₂'`-regular (in `L`), and for compatible
     Haar measures `haar'`, `haar`, every intertwining map `J : i_{P₁}^G(σ) → i_{P₂}^G(σ)`
     normalized by `(V, haar)` and every `J' : i_{P₁'}^L(σ) → i_{P₂'}^L(σ)` normalized by
     `(V', haar')` satisfy `i_Q^G(J')(f̃) = (J f)~` for all `f` and `f̃` as above.

By the VII.3.4 statement (clause 2 of `PQIntegralIntertwiningOperatorStatement`, applied in `G`
and in `L`) and the regularity conclusion, `J` and `J'` exist and are Renard's
`J^G_{P₂|P₁}(σ)` and `J^L_{(P₂∩L)|(P₁∩L)}(σ)`; the last item is Renard's
`J^G_{P₂|P₁}(σ) = i^G_Q(J^L_{(P₂∩L)|(P₁∩L)}(σ))` through the identifications.

## `PQIntertwiningOuterLeviStatement` (VII.3.5 (iii))

Binders: represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` with `l₂ ≫ p₂ = l₁ ≫ p₁`, and
`P̄₁ = MN̄₁` opposite to `P₁`; represented parabolics `Q₁ = LU₁`, `Q₂ = LU₂` of `G` with
`lQ₂ ≫ q₂ = lQ₁ ≫ q₁`, and `Q̄₁ = LŪ₁` opposite to `Q₁`; `P₁(F) ⊂ Q₁(F)` and
`P₂(F) ⊂ Q₂(F)`; one represented parabolic `P' = MN'` of `L` with
`l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁` and `P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`, Renard's
`P₁ ∩ L = P₂ ∩ L`; split components `a : A → M` and `aL : A_L → L`;
`V = N̄₁(F) ∩ N₂(F)` and `W = Ū₁(F) ∩ U₂(F)`, both in `G(F)`; `cᵢ(x) = δ_{Uᵢ}(x)^{1/2}`
computed in `Qᵢ`; `X = i_{P'}^L(σ)`.

Renard's hypothesis that `Qᵢ = PᵢL` is a parabolic subgroup with Levi factor `L` is encoded by
the given `Qᵢ = LUᵢ` with `Pᵢ ⊂ Qᵢ`: the unipotent radical `Uᵢ` of `Qᵢ` lies in that of
`Pᵢ`, so `Qᵢ = LUᵢ ⊂ LPᵢ ⊂ Qᵢ`, and `Qᵢ = PᵢL`.
Measures `haarW` on `W` and `haarV` on `V` are compatible when `∫_W φ dhaarW = ∫_V φ dhaarV`
for continuous compactly supported `φ : G(F) → ℂ`; Renard proves `W = V`.

The statement asserts:

1. for every Haar measure `haarW` on `W` there is a compatible Haar measure `haarV` on `V`;
2. for every smooth representation `σ` of `M(F)`:
   - every `f ∈ i_{P₁}^G(σ)` has an `f̃ ∈ i_{Q₁}^G(X)` (identification with `c₁`);
   - if `X` is `Q₁Q₂`-regular (for `aL`), then `σ` is `P₁P₂`-regular (for `a`), and for
     compatible Haar measures, every `J : i_{P₁}^G(σ) → i_{P₂}^G(σ)` normalized by
     `(V, haarV)` and every `J_Q : i_{Q₁}^G(X) → i_{Q₂}^G(X)` normalized by `(W, haarW)`
     satisfy `J_Q(f̃)(g)(x) = c₂(x)⁻¹ (J f)(emb(x) g)` whenever
     `f̃(g)(x) = c₁(x)⁻¹ f(emb(x) g)`: `J_Q(f̃) = (J f)~`, where the identification on the
     target side is that of `P₂ ⊂ Q₂`.

As for (ii), with the VII.3.4 statement this is Renard's
`J_{P₂|P₁}(σ) = J_{Q₂|Q₁}(i^L_{P₁∩L}(σ))` through the identifications.

## Provenance and departures from the source

The provenance is source: parts (ii) and (iii) of the Proposition of VII.3.5. Formal choices
and departures:

- **"Avec les identifications naturelles."** Renard fixes the identification in his proof by
  the formula `f̃(g)(l) = δ_U(l)^{-1/2} f(lg)`. The statements use this formula as a relation
  between `f` and `F` rather than constructing the isomorphism, assert that `f̃` exists, and
  express the operator identity by evaluation. Bijectivity of `f ↦ f̃` is not stated.
- **"Avec les notations évidentes."** `P ∩ L`, `N̄₁ ∩ L` and `P₁L` are encoded by represented
  parabolics of `L` or `G` characterized through point images, as described above.
- **Measures.** As in part (i), the operators depend on Haar measures. The statements quantify
  over compatible measures; compatibility expresses Renard's identifications
  `(N̄₁ ∩ L) ∩ (N₂ ∩ L) = N̄₁ ∩ N₂` and `Ū₁ ∩ U₂ = N̄₁ ∩ N₂`, and its existence clauses are
  their measure-theoretic content. The subgroup equalities themselves are not stated.
- **Semi-standard and standard.** Renard takes `P₁`, `P₂`, `Q` semi-standard and `L` standard
  in (iii). The statements do not assume this.
- **`PQ`-regularity** is `IsPQRegular`, condition (i) of the VII.3.3 Lemma, for the split
  component of the relevant Levi (`A_M` for `σ`, `A_L` for `i^L_{P₁∩L}(σ)`).
- **Universes.** `σ` has carrier in `Type v`; `i_{P'}^L(σ)` has carrier in `Type (max u v)`,
  and the outer functors are instantiated at `leviInductionFunctor.{u, max u v}`.

## Remaining obligations

The proofs are separate obligations. Renard's proof: for the regularity claims, comparison of
the ideals `I^{P₂,w̄}_σ` and `I^{(P₂∩L),w̄}_σ` through the double cosets
`W_M \ W_L / W_M ⊂ W_M \ W_G / W_M` in (ii), and the geometric lemma applied to
`w ∘ (r^L_{L∩w·(P₂L)} ∘ i^L_{P₁∩L}(σ))` with faithfulness of parabolic induction in (iii); for
the operator identities, the identification `f ↦ f̃`, the characterization of
`F̃^{<1̄}` by compact support on `N̄₁ ∩ N₂`, the integral formula, a cancellation of modular
characters in (iii), and uniqueness in VII.3.4.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements` | `IsIntegralIntertwiner`; through it the VII.3.4 objects, `leviPoints_locallyCompactSpace`, `leviPoints_nonarchimedeanGroup`, `HaarModulus.closedHalfCharacter`, `pointImage_comp_le` and Mathlib's measure theory |
