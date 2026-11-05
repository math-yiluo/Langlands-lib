# Existence of a special maximal compact subgroup for available Bruhat–Tits data: statement target

Worker 1249, task `219b673d-b7f3-47fb-9019-d1642687d4ac`.

This module states the general existence target
`Langlands.BruhatTits.SpecialCompact.AvailableSpecialMaximalCompactExistence`.
It is a proposition-valued definition, not a proof.

The witness data satisfy the full corrected KP Definition 4.1.26, as
formalized by `Langlands.Geometry.Building.KPBuildingAssignment.IsAvailableFor`
(module `Langlands.Geometry.Building.FullValidity.Assignment`, task
`129deca1-ce21-411b-9b79-7e94545fe26d`). This holds for `G` and for every
actual standard Levi subgroup, and `K_0` is the compact stabilizer of a
special vertex in the apartment of the same data. The earlier target
`SpecialMaximalCompactExistence` (module
`Langlands.BruhatTits.SpecialCompact.ExistenceStatement`) imposes only part of
these axioms. It stays published unchanged, and this target does not replace
it.

## Statement

For every universe level `u`, the target quantifies over:

- a nonarchimedean local field `F : Type u`, with
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
`hG.isAffineHom` and `hi.isSplitSubtorus.mono`, as in
`SpecialMaximalCompactExistence`.

The conclusion is that there exist an assignment
`𝔅 : KPBuildingAssignment.{u}` and apartment data
`D : KPApartmentData i (localFieldOrder F)` with the following properties.

1. `𝔅.IsAvailableFor F G hG`. This says Bruhat–Tits theory is available for
   `G` over `F` in `𝔅`: all ten axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8,
   4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22 of corrected Definition 4.1.26
   hold. These include the comparisons of Axiom 4.1.1 for central
   surjections out of `G`, the identifications of `B(G_der)` and `B(G_sc)`
   with `B(G)`, and Axiom 4.1.17 for isomorphisms out of `(F, G)`.
2. The data `𝔅.datum F G hG` of `𝔅` for `G` are based on the given torus
   and on `D`: `(𝔅.datum F G hG).base.S = S`,
   `HEq (𝔅.datum F G hG).base.i i` and
   `HEq (𝔅.datum F G hG).base.apartment D`. The apartment `A(S)` of the
   available data is therefore `D`.

There is also a point `x : D.Apartment` such that the following hold.

3. `D.IsSpecialApartmentVertex x`: `x` is a special point and a vertex of
   the affine root system of the reduced apartment (KP Definition 1.3.39).
4. `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)`. The
   subgroup `K_0 = D.specialCompactSubgroup x` unfolds to
   `D.compactStabilizer (D.apartmentMap x) = G(F)^1 ∩ G(F)_x`. It is
   algebraically bounded, open and maximal among bounded subgroups. It is
   compact, open and maximal among compact subgroups. Every element of the
   relative Weyl group `N(F)/Z(F)` has a representative in `N(F) ∩ K_0`. For
   every `J ⊆ simpleRelativeRoots i ν`, the identity
   `K_0 ∩ P_J = (K_0 ∩ M_J)(K_0 ∩ U_J)` holds literally in `G(F)`.
5. Let `J ⊆ simpleRelativeRoots i ν`, and let `M_J = Standard.leviScheme i ν J`
   be the actual standard Levi with the torus
   `Standard.leviTorusHom i ν J : S → M_J`. The instances on them are the
   published ones used in `SpecialLeviInheritance`. Then there are
   `hM : IsConnectedReductive M_J` and
   `DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F)`
   such that:
   - `𝔅.IsAvailableFor F M_J hM`, so Bruhat–Tits theory is available for
     `M_J` in the same assignment `𝔅`;
   - `(𝔅.datum F M_J hM).base.S = S`,
     `HEq (𝔅.datum F M_J hM).base.i (Standard.leviTorusHom i ν J)` and
     `HEq (𝔅.datum F M_J hM).base.apartment DM`;
   - there is a point `xM` with `SpecialLeviRestriction F ν D x J DM xM`.
     That is, `xM` is a special vertex of the apartment of `DM` and is
     restricted from `x` (KP Lemma 6.7.1). Its compact stabilizer has the
     properties of item 4 for `(M_J, S, ν)`, and it is the preimage of `K_0`
     in `M_J(F)`, whose image in `G(F)` is `K_0 ∩ M_J(F)`.

The same `𝔅`, `D` and `x`, and hence the same `K_0`, are used in all clauses
and for every `J`.

The predicates `SpecialCompactProperties`, `SpecialLeviRestriction` and
`SpecialLeviInheritance` are documented in
`Langlands.BruhatTits.SpecialCompact.Properties`. The subgroup and the vertex
predicate are Worker 1229's adapters in
`Langlands.Geometry.Building.SpecialCompact`.

## Formulation choices

- **Matching the torus.** In `KPBuildingDatum G`, the maximal split torus
  `S`, its inclusion `i` and the apartment `A(S)` are fields of
  `base : ParahoricBuildingData G`, which extends `ValuationBuildingData G`.
  They are part of the assignment. The target names the torus `i` and the
  apartment `D` explicitly, as `SpecialMaximalCompactExistence` does, and
  requires the data of `𝔅` to have exactly this torus and apartment. Since
  the type of `base.i` depends on `base.S`, and the type of `base.apartment`
  on `base.i`, these equalities are stated as `base.S = S` together with
  heterogeneous equalities (`HEq`). Together they say that the triple
  `(base.S, base.i, base.apartment)` is `(S, i, D)`. With them, `K_0` and
  `xM` are the subgroup and the point of the available data themselves. The
  centralizer, zero-subgroup, integral-model and other fields of the data are
  not constrained beyond `IsAvailableFor`.
- **Levi reductivity.** `𝔅.datum` takes a proof that the group is connected
  reductive. The Library has no unconditional lemma that `Standard.leviScheme
  i ν J` is connected reductive, so clause 5 asserts it with the existential
  `hM`. `IsConnectedReductive` is a proposition, so the data `𝔅.datum F M_J hM`
  do not depend on the choice of `hM`.
- **The assignment.** `𝔅` assigns data to every connected reductive group
  over every nonarchimedean local field in universe `u`. The target asks
  for availability only at `G` and at the `M_J`, as in KP's phrase
  "Bruhat–Tits theory is available for `G` over `k`". The global condition
  `𝔅.IsValid` is not required. `𝔅` may depend on `(F, G, S, i, ν)`: the base
  torus of the data is part of the assignment, so a single assignment cannot
  have every maximal split torus as its base torus.
- **Separate Levi data.** Each `M_J` has its own data in the same `𝔅`. The
  relation to `G` is `SpecialLeviRestriction`, which compares valuations
  through the restriction of KP Lemma 6.7.1 and compares compact stabilizers
  inside `M_J(F)`. The target does not state that the building of `M_J`
  embeds in that of `G`.

## Relation to the other targets of this task

- `SpecialMaximalCompactExistence` (`ExistenceStatement`) asks only for
  `KPApartmentData` satisfying `SatisfiesApartmentAxioms` (V 6 on `Z(F)`, V 7,
  AS 2–AS 5) and Axiom 4.1.2. The full predicate contains these clauses for
  the base data `B`. The field `affineRootSystem.apartmentAxioms` gives
  `B.apartment.SatisfiesApartmentAxioms B.centralizer`, and the field
  `boundedSubgroups` gives `B.apartment.HasBoundedOpenStabilizers`. By clause
  2, `B.apartment` is `D`. Informally, this target therefore implies the
  earlier one, with the centralizer of the data as the witness `C`. No
  implication between the two targets is proved in Lean, and the earlier
  target is kept as published.
- `ParahoricLeCompactStabilizer` (`ParahoricStatement`) states
  `P.parahoricAt x ≤ P.apartment.specialCompactSubgroup x` for all
  `P : ParahoricBuildingData G`. In this target `(𝔅.datum F G hG).base` is
  such a `P`, and by clause 2 its apartment is `D`. So, after transporting
  `x` along the equalities of clause 2, that target applies to the `K_0`
  here.
- `SharpFixerLeCompactStabilizer` (`SharpFixerStatement`) is the inclusion
  `G(F)^♯_x ⊆ K_0`.
- Renard V.5.1(1) (Iwasawa) and (4) (Cartan) are sibling tasks and are not
  stated here.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 1.3.39, Lemma 1.3.42 and Proposition 1.3.43 (PDF pages 60–61);
  Definition 2.2.1 and Fact 2.2.3 (PDF page 101); Axioms 4.1.1–4.1.22 and
  Definition 4.1.26 (PDF pages 188–196), including Definition 4.1.3 and the
  discussion after it (PDF page 189); Theorem 4.2.15(1) and its proof (PDF
  pages 204–205); §6.7, Lemma 6.7.1 and §6.7.2 (PDF pages 264–265); Remark
  7.4.2, the comparison of the sharp fixer with the parahoric (PDF page 286);
  the standing assumptions of Chapter 9 (PDF page 354); Theorem 9.2.7 (PDF
  page 360) and its proof in §9.5 (PDF pages 394–395).
- Corrections `kaletha-prasad-2024-corrections`, 1 November 2024, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  the Henselian convention for §2.2 (PDF page 24); the replacement of Remark
  2.5.15 (PDF pages 24–25); the corrections to §4.1
  and §4.2 (PDF pages 27–29), including the corrected list of axioms in
  Definition 4.1.26 (PDF page 27); the assumption of AS 5 in Chapter 7 (PDF
  page 33). The corrections amend axioms and proofs of Chapter 4, but not the
  statement of Theorem 4.2.15. No correction to Definition 1.3.39 or Lemma
  6.7.1 is listed.
- Renard, 9 July 2026 edition,
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  Théorème V.5.1, printed page 122, PDF page 128.

Chapter 9 assumes that `k` has a discrete valuation with Henselian valuation
ring and perfect residue field (PDF page 354). Every nonarchimedean local
field satisfies these assumptions. Under them, KP Theorem 9.2.7 (PDF page 360)
states that Bruhat–Tits theory is available for every connected reductive
`k`-group, with the book's list of axioms 4.1.1, 4.1.4, 4.1.6, 4.1.9, 4.1.17,
4.1.20 and 4.1.22. Its proof in §9.5 (PDF pages 394–395) also verifies
Axioms 4.1.2 and 4.1.8 of the corrected list. §9.5 does not name Axiom
4.1.16. For quasi-split groups, KP prove it in Corollary 7.4.9 (cited in
§4.1.28, PDF page 197). This target asserts all ten axioms of the corrected
list, including 4.1.16.

Given available data, Theorem 4.2.15(1) gives the properties of `K_0` at a
special vertex. Its bounded form is the source form, and the compact form
follows over a local field by Fact 2.2.3. Renard V.5.1 gives (2), (3) and
(5). By Axiom 4.1.1 there are apartments `A(S′)` for all maximal split tori
`S′`, so the data can be based at the given torus `S`. This target
transcribes these results for the published objects. It does not prove
them.

## Map to Renard V.5.1

| Renard V.5.1 | This target |
| --- | --- |
| `K_0` open maximal compact | `IsCompactOpenMaximal F K_0`, with `IsBoundedOpenMaximal F K_0` as the KP 4.2.15(1) form |
| (2) every `s ∈ W_G` has a representative in `K_0` | `HasWeylRepresentatives i K_0` |
| (3) `K_0 ∩ P = (K_0 ∩ M)(K_0 ∩ N)` for standard `P = MN` | `HasParabolicFactorization i ν K_0` |
| (5) `K_0 ∩ M` satisfies the properties for `P_∅ ∩ M` | clause 5: available data for `M_J` in the same `𝔅`, with apartment `DM` and `SpecialLeviRestriction F ν D x J DM xM` |
| (1) Iwasawa, (4) Cartan | sibling targets, not stated here |

## Scope and distinctions

`K_0` is `G(F)^1 ∩ G(F)_x`. It is not the full reduced fixer
`D.reducedFixer`, and it is not the parahoric `P_x = Z(F)^0 · G(F)^♯_x` (KP
Definition 7.4.1(4)). When the center of `G` contains a nontrivial split
torus, its noncompact group of rational points acts trivially on the reduced
building. It then lies in the full fixer but not in `K_0`.

`P_x` may be strictly smaller than `K_0`. Right after Definition 4.1.3 (PDF
page 189), KP note that the stabilizer `G(F)^0_x` of `x` in `G(F)^0`, which is
`P_x`, may be a proper subgroup of the stabilizer `G(F)^1_x` in `G(F)^1`. The
corrected Remark 2.5.15 (corrections, PDF pages 24–25) gives an example: the
norm-one torus `T` of a ramified separable quadratic extension, for which
`T(F)^0` has index two in `T(F)^1 = T(F)`. Such a `T` is anisotropic, so its
reduced building is a single point, and the example is an instance of the
rank-zero case described below. KP Remark 7.4.2 (PDF page 286)
compares a different pair: the sharp fixer `G(F)^♯_x` with `P_x`.

The compact and bounded forms are both stated directly. Their comparison is
the separate published statement `LocalFieldAffineBoundedCompactnessProperty`
(KP Fact 2.2.3), and it is not assumed.

The rank-zero case is included. For `J = ∅`, the Levi `M_∅ = Z_G(S)` has no
relative roots, and `G` itself may have none. The apartment axioms inside
`IsAvailableFor` are the Library's `SatisfiesApartmentAxioms`. These use the
rank-zero form of AR 1 (`IsAffineRootSystemWithRankZero`), so they admit an
empty affine root system on a one-point apartment.
