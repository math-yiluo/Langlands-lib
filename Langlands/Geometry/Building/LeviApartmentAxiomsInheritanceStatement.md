# The apartment axioms pass to the restriction to a standard Levi subgroup

`Langlands.Geometry.Building.LeviApartmentAxiomsInheritanceStatement` is a
Prop-valued `def` at every universe `u`. It states that the axioms on an
apartment class collected in the Library predicate
`KPApartmentData.SatisfiesApartmentAxioms` (V 6 on the centralizer, V 7 and
AS 2–AS 5) pass from a connected reductive group to the restriction of its
apartment class to a standard Levi subgroup at the same maximal split torus,
over a nonarchimedean local field. The module supplies no proof.

## Statement

The proposition quantifies over:

- every nonarchimedean local field `F`, of either characteristic;
- every group scheme `G` over `Spec F` with `hG : IsConnectedReductive G`;
- every maximal split torus `i : S → G` (`hi : IsMaximalSplitTorus i`) and
  every cocharacter `ν` of `S` with `IsGenericCocharacter i ν`, so that `ν`
  determines a positive system of relative roots;
- every subset `J` of the simple relative roots `simpleRelativeRoots i ν`, with
  the actual standard Levi subgroup `M_J = Standard.leviScheme i ν J`, its
  inclusion `j = Standard.leviHom i ν J : M_J → G`, and the same torus
  `iM = Standard.leviTorusHom i ν J : S → M_J`, as in the published
  `LeviApartmentRestrictionStatement`;
- centralizer data `C : CentralizerDatum i` and
  `CM : CentralizerDatum iM` (representations of the actual centralizers of
  `S` in `G` and in `M_J`);
- apartment data `D : KPApartmentData i (localFieldOrder F)` and
  `DM : KPApartmentData iM (localFieldOrder F)`.

The premises are:

1. some point `x` of `D` and some point `xM` of `DM` satisfy
   `IsLeviRestriction j x xM`: for every relative root `a` of `(M_J, S)` and
   every `m ∈ M_J(F)`, `xM_a(m) = x_a(j(m))`. As `DM` is an equipollence class
   and restriction commutes with translation, this makes `DM` the class
   `A(M_J, S)` of KP §6.7;
2. `D.SatisfiesApartmentAxioms C`.

The conclusion is `DM.SatisfiesApartmentAxioms CM`. The predicate
`KPApartmentData.SatisfiesApartmentAxioms` (module
`Langlands.Geometry.Building.KPApartmentAxioms`) consists of: V 6 for every
valuation of the class and every rational point of the centralizer
(`IsOmegaCompatible`); V 7 (`IsTopologyCompatible`); AS 2 and AS 3 (the
extended affine roots `Ψ′` and the affine roots `Ψ` are affine root systems,
allowing rank zero, with derivative the relative roots); AS 4; and the three
sentences of AS 5 (the image of the normalizer points contains `W(Ψ)` and lies
in `W(Ψ)^ext`; it equals `W(Ψ)` for simply connected groups; it equals
`W(Ψ)^ext` for quasi-split adjoint groups).

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- §6.7 and Lemma 6.7.1, printed p.233 / PDF p.264: for a Levi subgroup `M`
  containing the maximal split torus `S`, `A(M, S) = {φ_M | φ ∈ A(S, G)}`.
  Lemma 6.7.1: (1) each `φ_M` is a valuation of the root datum of `(M, S)`;
  (2) if `φ` is compatible with `ω`, then so is `φ_M`; (3) `A(M, S)` is an
  equipollence class. The proof says that V 1–V 6 for `φ` imply them for
  `φ_M`.
- §6.7.2, printed pp.233–234 / PDF pp.264–265: under the projection,
  `Ψ(M, S) ⊂ Ψ(S, G)` and `Ψ′(M, S) ⊂ Ψ′(S, G)`.
- Definition 6.1.2, printed p.199 / PDF p.230, states V 6 and V 7.
- Axiom 4.1.6 and Remark 4.1.7, printed pp.159–160 / PDF pp.190–191: AS 1–AS 5;
  by Remark 4.1.7, AS 1–AS 4 already imply that the image of `N(k)` contains
  `W(Ψ)` and lies in `W(Ψ)^ext`.
- Proposition 6.2.1, printed pp.212–214 / PDF pp.243–245, is AS 1 for every
  valuation (proved in the Library as `rootReflection`).
- KP 4.1.28, printed p.166 / PDF p.197: AS 2–AS 4 are Propositions 6.3.13 and
  6.3.8, and AS 5 is Proposition 6.6.2 for quasi-split groups.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p.33: AS 1–AS 4 are proved in §6.3 for every valuation, and AS 5 is assumed in
Chapter 7. For general `G` it amounts to the assertion for the simply
connected case and is proved in Proposition 9.4.35 when the residue field is
perfect. The Chapter 6 corrections on PDF p.32 do not concern §6.7.

## Derived scope and provenance

This is a derived formulation. KP do not state an inheritance result for the
axioms of the whole class; the statement assembles the following facts for
the restricted class.

- **V 6** is Lemma 6.7.1 (2), for the centralizer of `S` in `M_J`, which is
  the centralizer of `S` in `G`.
- **V 7** concerns the same root groups with the topology of the closed
  subgroup `M_J(F)` of `G(F)`.
- **AS 2–AS 4** hold for every valuation by KP §6.3, applied to `M_J` and the
  valuation `φ_M` of Lemma 6.7.1 (1). They can also be obtained from those of
  `D` through §6.7.2.
- **AS 5.** Its first sentence follows from AS 1–AS 4 (Remark 4.1.7). Its
  second and third sentences concern only a semisimple `M_J`. A standard Levi
  subgroup `M_J` has a split central torus of dimension
  `dim S − |J|`, so it is semisimple only when `J` is the whole set of simple
  roots and `G` has no split central torus. In that case `M_J = G`, and these
  sentences come from `D`.

Further scope:

- **Field.** The statement covers nonarchimedean local fields, of mixed and
  equal characteristic.
- **Levi subgroups.** Only the actual standard Levi subgroups `M_J` at the
  same torus are covered, as in `LeviApartmentRestrictionStatement` and
  `LeviSpecialPointRestrictionStatement`. Every Levi subgroup containing `S` is
  `N(F)`-conjugate to a standard one.

No existence of `C`, `CM`, `D` or `DM` is asserted. With
`ChapterSevenBuildingAxiomsStatement` and `RootGroupActionAxiomStatement`
applied to building data for `M_J` built from `DM` and `CM`, this statement
gives the building axioms for the Levi subgroup under hypotheses on `G`
alone, as needed for local Levi arguments such as Task 5309.

## Expected proof route (not prescribed)

Use the published restriction results: Worker 164's
`Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction` and
`LeviValuationRestriction` (restricted families, projection, translation
compatibility), Worker 163's
`isOmegaCompatible_standardLevi_of_restriction` (module
`Langlands.Representation.Plancherel.RenardLeviCentralizerCompatibility`; full
V 6 for a restricted class and the standard Levi centralizer datum; for an
arbitrary `CM` one also needs independence of the centralizer
representative), and the restriction of affine roots
(`LeviSpecialPointRestrictionStatement`, proof Task 5415). For AS 5 use
`rootReflection` for the Levi data, the normalizer action on affine roots
(`NormalizerAffineRootAction`), and the dimension count for the central torus
of `M_J`.
