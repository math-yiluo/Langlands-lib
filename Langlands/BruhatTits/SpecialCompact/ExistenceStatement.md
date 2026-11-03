# Existence of a special maximal compact subgroup: statement target

Worker 1249, task `219b673d-b7f3-47fb-9019-d1642687d4ac`.

This module states the general existence target
`Langlands.BruhatTits.SpecialCompact.SpecialMaximalCompactExistence`. It is
a proposition-valued definition, not a proof.

Scope: this target is supplementary. Its witness data satisfy only the axiom
predicates listed under "Conditions on the witness data". It does not state,
and does not discharge, existence for apartment data satisfying the full
corrected KP Definition 4.1.26 (for `D` and for every Levi `DM`). That
existence remains open. The inclusion `P_x ⊆ K_0` is not part of this
target; it is the separate target `ParahoricLeCompactStabilizer` (see "Scope
and distinctions").

## Statement

For every universe level, the target quantifies over:

- a nonarchimedean local field `F`, with
  `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`.
  Both mixed and equal characteristic are included, with no tameness,
  residue-characteristic or splitness restriction;
- a group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`;
- a commutative group scheme `S` with `i : S.toGrp ⟶ G` and
  `hi : IsMaximalSplitTorus i`, the explicitly chosen maximal split torus;
- `ν : cocharacterLattice S` with `IsGenericCocharacter i ν`. This chooses
  the positive system, and so the minimal parabolic `P_∅` and its simple roots
  `simpleRelativeRoots i ν`.

The instances `IsAffineHom G.X.hom` and `Mono i.hom.hom.left` are taken from
`hG.isAffineHom` and `hi.isSplitSubtorus.mono`.

The conclusion is that there exist a centralizer datum `C : CentralizerDatum i`
and apartment data `D : KPApartmentData i (localFieldOrder F)` such that

1. `D.SatisfiesApartmentAxioms C` (Worker 1045's
   `Langlands.Geometry.Building.KPApartmentAxioms`): V 6 on the actual
   centralizer `Z(F)`, V 7, AS 2, AS 3, AS 4 and all three sentences of AS 5;
2. `D.HasBoundedOpenStabilizers`: KP Axiom 4.1.2 for the reduced building of
   `D`;

and a point `x : D.Apartment` such that

3. `D.IsSpecialApartmentVertex x`: `x` is a special point and a vertex of
   the affine root system `D.affineRoots` of the reduced apartment (KP
   Definition 1.3.39; see Lemma 1.3.42 and Proposition 1.3.43);
4. `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)`: the actual
   `K_0 = D.specialCompactSubgroup x`, which unfolds to
   `D.compactStabilizer (D.apartmentMap x) = G(F)^1 ∩ G(F)_x`, has the
   following properties. It is algebraically bounded, open and maximal among
   bounded subgroups. It is compact, open and maximal among compact
   subgroups. Every element of the relative Weyl group `N(F)/Z(F)` has a
   representative in `N(F) ∩ K_0`. For every `J ⊆ simpleRelativeRoots i ν`,
   `K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` holds literally in `G(F)`;
5. for every `J ⊆ simpleRelativeRoots i ν`, with the published instances on
   the actual standard Levi `M_J = Standard.leviScheme i ν J` and on the torus
   `Standard.leviTorusHom i ν J : S → M_J` (the same instances as in
   `SpecialLeviInheritance`), there exist
   `CM : CentralizerDatum (Standard.leviTorusHom i ν J)` and
   `DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)`
   with `DM.SatisfiesApartmentAxioms CM`, `DM.HasBoundedOpenStabilizers`, and a
   point `xM` with `SpecialLeviRestriction F ν D x J DM xM`. That is, `xM` is a
   special vertex of the apartment of `DM` restricted from `x` (KP Lemma
   6.7.1). Its compact stabilizer has the properties of item 4 for
   `(M_J, S, ν)` and is the preimage of `K_0` in `M_J(F)`, whose image in
   `G(F)` is `K_0 ∩ M_J(F)`.

Clause 5 is `SpecialLeviInheritance F hi ν D x` from `Properties` with, for
each `J`, the two axiom predicates added for the Levi data. So the target
implies `SpecialLeviInheritance F hi ν D x`. The predicates `SatisfiesApartmentAxioms`
and `HasBoundedOpenStabilizers` assume no reductivity of the group, so they
apply verbatim to `(M_J, S)`.

The predicates are documented in `Langlands.BruhatTits.SpecialCompact.Properties`.
The subgroup and vertex predicate are Worker 1229's accepted adapters in
`Langlands.Geometry.Building.SpecialCompact`. The same witness `(C, D, x)`,
and hence the same `K_0`, is used in all clauses and for every `J`.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 1.3.39, Lemma 1.3.42 and Proposition 1.3.43 (PDF pages 60–61);
  Definition 2.2.1 and Fact 2.2.3 (PDF page 101); Axiom 4.1.2 (PDF page
  189); Axioms 4.1.4 and 4.1.6 (PDF pages 190–191); Theorem 4.2.15(1) and its
  proof (PDF pages 204–205); Definition 6.1.2, V 6 and V 7 (PDF page 230);
  Proposition 6.3.8 and Proposition 6.3.13 (PDF pages 249–252); §6.7, Lemma
  6.7.1 and §6.7.2 (PDF pages 264–265); the hypotheses opening Chapter 7 (PDF
  pages 266–267).
- Corrections `kaletha-prasad-2024-corrections`, 1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  the Henselian convention for §2.2 (PDF page 24); the corrections to §4.1
  and §4.2 (PDF pages 27–29), including the corrected Definition 4.1.26 (PDF
  page 27); the assumption of AS 5 in Chapter 7 (PDF page 33). The
  corrections to §4.1 and §4.2 amend axioms and proofs used by Chapter 4, but
  not the statement of Theorem 4.2.15. No correction to Definition 1.3.39 or
  Lemma 6.7.1 is listed.
- Renard, 9 July 2026 edition,
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  Théorème V.5.1, printed page 122, PDF page 128.

Example 4.2.16 is not cited as the maximality theorem. A general maximal
bounded subgroup need not fix a vertex; this target concerns the special-vertex
choice only.

## Map to Renard S19

Renard V.5.1 asserts the existence of an open maximal compact subgroup `K_0`
of `G` with properties (1)–(5) relative to `P_∅ = M_∅ N_∅`.

| Renard V.5.1 | This target |
| --- | --- |
| `K_0` open maximal compact | `IsCompactOpenMaximal F K_0`, with `IsBoundedOpenMaximal F K_0` as the KP 4.2.15(1) form |
| (2) every `s ∈ W_G` has a representative in `K_0` | `HasWeylRepresentatives i K_0` |
| (3) `K_0 ∩ P = (K_0 ∩ M)(K_0 ∩ N)` for standard `P = MN` | `HasParabolicFactorization i ν K_0` |
| (5) `K_0 ∩ M` satisfies the properties for `P_∅ ∩ M` | clause 5: Levi data `DM` with the same axiom predicates and `SpecialLeviRestriction F ν D x J DM xM` (this implies `SpecialLeviInheritance F hi ν D x`) |
| (1) Iwasawa, (4) Cartan | sibling targets, not stated here |

## Conditions on the witness data

The witness data range over the published `KPApartmentData`. These are an
`N(F)`-stable equipollence class of valuations of the root datum (V 0–V 5),
compatible with `ω` on `S(F)`, with the action of `N(F)` of KP §6.1.8. The
target asserts that suitable data exist, not that every such `D` has these
properties.

The witness `D`, and each Levi witness `DM`, must in addition satisfy
`SatisfiesApartmentAxioms` and `HasBoundedOpenStabilizers`:

- V 6 on all of `Z(F)` for the actual centralizer `C`, so that the valuations
  are compatible with `ω` in KP's sense. Under V 6 each `z ∈ Z(F)` acts on the
  apartment by the translation `ν(z)` (proved in `KPApartmentAxioms`), the
  `Z(F)`-part of KP Axiom 4.1.4 (A 1);
- V 7 for the published topology `rationalPointTopology F G.X`;
- AS 2, AS 3 and AS 4 of KP Axiom 4.1.6, which KP prove for `A(S)` in §6.3
  (Propositions 6.3.8(2) and 6.3.13);
- all three sentences of AS 5, which KP assume in Chapter 7 (corrections, PDF
  page 33);
- KP Axiom 4.1.2 for the reduced building of the data.

The predicates are consistent in rank zero. For `J = ∅` the Levi
`M_∅ = Z_G(S)` has no relative roots, and the same holds for `G` itself when
`G` has no relative roots. Then the apartment is a point and `Ψ = ∅` is the
rank-zero affine root system on it. `SatisfiesApartmentAxioms` uses
`IsAffineRootSystemWithRankZero`
(`Langlands.Geometry.Building.RankZeroAffineRootSystem`), whose AR 1 asks
that `∇Ψ` span `V*`, so it admits this case. There
`SatisfiesApartmentAxioms` is equivalent to V 6
(`satisfiesApartmentAxioms_iff_of_relativeRoots_eq_empty` in
`KPApartmentAxioms`).

These are only the part of the standing hypotheses of KP Chapter 7 (PDF
pages 266–267 and the correction on PDF page 33) that concerns the single
class `A(S)`: an equipollence class of valuations compatible with `ω`, with
the `N(F)`-action of §6.1.8 and AS 5, together with Axiom 4.1.2. Chapter 7
also assumes Axiom 4.1.4 for all maximal split tori `S′`, with apartments
`A(S′)` and the conjugation maps `A(S) → A(gSg⁻¹)`. That family is not
imposed here.

They are not the full corrected Definition 4.1.26 (corrections, PDF page
27), which requires Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16,
4.1.17, 4.1.20 and 4.1.22. Not imposed here:

- AS 1 and the `m(u)`-form of AS 2 of Axiom 4.1.6. They need the elements
  `m(u)` of KP Proposition 2.11.17, which are not in the Library;
- Axiom 4.1.4 beyond the single apartment `A(S)`: the apartments `A(S′)`
  for all maximal split tori and the isomorphisms `A(S) → A(gSg⁻¹)`;
- AS 6 of Axiom 4.1.6, and Axioms 4.1.1, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20
  and 4.1.22. They concern the building's polysimplicial structure, all
  apartments, the groups `G(F)^0`
  and `Z(F)^0` of KP Definition 2.6.23 (now defined from chosen data in
  `Langlands.Geometry.Building.KPZeroSubgroups`, but these axioms about them
  are not formalized), the Tits system
  of Axiom 4.1.9, the integral models of Axioms 4.1.20 and 4.1.22, and the
  functoriality of `G ↦ B(G)`. They are not conditions on one class `A(S)`.

KP Chapter 7 constructs the building and proves the other properties from
the Chapter 7 hypotheses. That derivation is not formalized. A formal
predicate for the full corrected Definition 4.1.26 does not exist yet. For
this reason the target is supplementary: the existence of data satisfying the
full corrected Definition 4.1.26, for `G` and for every standard Levi, is not
asserted here and remains open.

## Scope and distinctions

`K_0` is `G(F)^1 ∩ G(F)_x`, not the full reduced fixer `D.reducedFixer` and
not the parahoric `P_x = Z(F)^0 · G(F)^♯_x` (KP Definition 7.4.1(4)). When
the center of `G` contains a nontrivial split torus, its noncompact group of
rational points acts trivially on the reduced building and so lies in the
full fixer but not in `K_0`. `P_x` may be strictly smaller than `K_0`. The inclusion
`P_x ⊆ K_0` is the separate target
`Langlands.BruhatTits.SpecialCompact.ParahoricLeCompactStabilizer` (module
`Langlands.BruhatTits.SpecialCompact.ParahoricStatement`). It is stated for
every `P : ParahoricBuildingData G`, a structure that adds a zero-subgroup
datum for `Z(F)^0` and `G(F)^0` to the building data. The witness data of
this target carry no such datum, so the two targets are not linked in Lean.
Its factor `G(F)^♯_x ⊆ K_0` is the separate target
`Langlands.BruhatTits.SpecialCompact.SharpFixerLeCompactStabilizer`.

The compact and bounded forms are both stated directly. Their comparison is
the separate published statement
`LocalFieldAffineBoundedCompactnessProperty` (KP Fact 2.2.3) and is not
assumed.
