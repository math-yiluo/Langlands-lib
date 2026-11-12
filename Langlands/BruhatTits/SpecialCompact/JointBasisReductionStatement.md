# Reduction of the joint special-compact existence target

`Langlands.BruhatTits.SpecialCompact.JointBasisReductionStatement` is a
proposition target. It is an implication: the joint special-compact, Iwasawa,
Cartan and simultaneous-basis existence target
`JointSpecialCompactBasisExistenceStatement` follows from the existence of a
valid corrected Kaletha–Prasad assignment together with six conditional
statements on valid or available data. The declaration states this
implication; it supplies no proof. None of the premises is asserted.

## The statement

All premises and the conclusion are taken at the same universe `u`. The premises
are, in order:

1. `∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid`: some assignment satisfies the
   full corrected KP Definition 4.1.26 for every connected reductive group over
   every nonarchimedean local field in universe `u`. This is the content of the
   KP program's target `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`
   (KP Theorem 9.2.7, Definition 4.1.26 part), written out here so that the
   reduction does not depend on that module.
2. `ValidAssignmentTorusRebasingStatement`: a valid assignment can be rebased so
   that its data for a given `G` sit at any prescribed maximal split torus.
3. `AvailableSpecialVertexExistenceStatement`: the apartment of available data
   contains a special vertex (KP Proposition 1.3.43).
4. `AvailableSimultaneousStandardBasisStatement`: at every special vertex of
   the data of a valid assignment, the compact properties, geometric Levi
   inheritance and the simultaneous normal compact-open basis hold for the
   common `K_0` (Renard V.5.1–V.5.2).
5. `Iwasawa.AvailableIwasawaStatement`: for available data, at every special
   vertex, the parabolic point products for `K_0` (Renard V.5.1(1); KP Theorem
   5.3.4).
6. `Plancherel.RenardCartan.AvailableRenardCartanStatement`: for available
   data, at every special vertex, Renard's Cartan comparison and its
   same-compact standard-Levi compatibility, with the torus centralizer
   carried by the data (Renard V.5.1(4)–(5)).
7. `AvailableSpecialLeviCompactStatement`: for a valid assignment, the preimage
   of `K_0` in each actual standard Levi is the special compact subgroup, at a
   special vertex, of available data for the Levi at the same torus (Renard
   V.5.1(5)).

The conclusion is `JointSpecialCompactBasisExistenceStatement.{u}`, unchanged.
It quantifies over every universe-`u` field `F` with `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`, every connected reductive
`G/Spec F`, every maximal split torus inclusion `i : S.toGrp ⟶ G` and every
generic cocharacter `ν` of `S`. Its existential `D`, `x`, `Z`, `j`, `s` and
character-restriction bijectivity witness `h` are shared by all its clauses.
There is no restriction on characteristic, residue characteristic, rank,
splitness, quasi-splitness or tameness.

Premise 1 is an existence statement. Premises 2–7 are conditional statements:
each assumes validity or availability and asserts properties of the assigned
data. The reduction uses no other hypothesis, and in particular none of the
conjuncts of the target appears as a premise at the target's witnesses.

## How the premises combine

Fix `F`, `G`, a maximal split torus `i : S → G` and a generic `ν`. Premises 1
and 2 give a valid assignment whose data `B` for `G` have torus `S` and
inclusion `i`. Premise 3 gives a special vertex `x` of `B.apartment`. Take
`D := B.apartment`, this `x`, and for `Z`, `j`, `s` and `h` the torus centralizer
recorded in `B` (`B.centralizer`). Premise 4 gives the compact properties, Levi
inheritance and simultaneous basis at `K_0 = D.specialCompactSubgroup x`.
Premise 5 gives the ambient Iwasawa products. Premise 6 gives both Cartan
clauses with the same `Z`, `j`, `s` and `h`. For every `J`, premise 7 gives
available Levi data at the same torus whose special compact subgroup is the
preimage of `K_0`, and premise 5 for the Levi gives the Levi Iwasawa products.
This describes the intended common-witness construction; implementing the
transports and proving the implication belong to a separate proof task.

## Sources and provenance

The reduction is internal packaging of published and companion targets; it
records the proposed implication rather than an additional source theorem.
Neither Kaletha–Prasad nor Renard states this exact formulation. The sources
of the individual premises are cited in their own Markdown. The main ones are:

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition
  1.3.43, printed p.30/PDF p.61; Definition 4.1.26, printed p.165/PDF p.196;
  Theorem 5.3.4, printed p.190/PDF p.221; Theorem 9.2.7, printed p.329/PDF
  p.360. The last theorem is the source of the separate existence premise,
  not a result supplied by this reduction.
  Source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.27.
  Source ID `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
  V.5.1–V.5.2, printed pp.122–123/PDF pp.128–129. Source ID
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
