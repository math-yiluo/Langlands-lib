# Bruhat–Tits theory is available for every connected reductive group

`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` is a
Prop-valued `def` at every universe `u`:

```
def BruhatTitsAvailabilityStatement : Prop :=
  ∃ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid
```

It states the corrected Definition 4.1.26 part of the conclusion of
Kaletha–Prasad Theorem 9.2.7, over nonarchimedean local fields: Bruhat–Tits
theory is available for every connected reductive group. The module supplies
no proof.

## Statement

`KPBuildingAssignment.{u}` (module
`Langlands.Geometry.Building.FullValidity.Assignment`) chooses data
`KPBuildingDatum G` for every nonarchimedean local field `F` in universe `u`
and every group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]` and
`IsConnectedReductive G`. The
data are the parahoric building data of `G` (reduced building, apartment of a
maximal split torus, root groups and valuations, `G(F)^0`, `Z(F)^0`), a
polysimplicial realization, an apartment splitting, an indexed family of
integral models over `𝒪[F]` with their morphisms and split tori, special-fibre
radicals and quotients, and relative root reflection data.

`𝔅.IsValid` says that `𝔅.IsAvailableFor F G hG` holds for every such `F`, `G`
and `hG`. `IsAvailableFor` is a structure with one field for each axiom of
corrected Definition 4.1.26: 4.1.1 (including the comparisons for surjections
with central kernel out of `G` and the identifications with the buildings of
the derived subgroup and its simply connected cover), 4.1.2, 4.1.4, 4.1.6,
4.1.8, 4.1.9, 4.1.16, 4.1.17 (every valued-field isomorphism out of `F` and
every isomorphism of `G` with a group over the target field), 4.1.20 and
4.1.22. The statement asserts that one assignment satisfies all of them at
once. A single assignment is needed because Axioms 4.1.1 and 4.1.17 compare
the data assigned to different groups and fields.

## Source correspondence

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Definition 4.1.26, printed p.165 / PDF p.196: Bruhat–Tits theory is
  available for `G` over `k` if the listed axioms hold.
- Theorem 9.2.7, printed p.329 / PDF p.360: for a connected reductive group
  `G` over a discretely valued field `k` with Henselian valuation ring and
  perfect residue field, the descended building `B(G_K)^Γ`, with its
  apartments, polysimplicial structure and the group schemes of 9.2.5,
  fulfils Axioms 4.1.1, 4.1.4, 4.1.6, 4.1.9, 4.1.17, 4.1.20 and 4.1.22, "thus,
  Bruhat–Tits theory is available for G. Moreover, Axiom 4.1.27 holds." The
  chapter introduction (printed p.323 / PDF p.354) states that Chapters 6–8
  make the theory available for the quasi-split group `G_K`.

The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.27, replace the axiom list of Definition 4.1.26 by Axioms 4.1.1, 4.1.2,
4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. The
corrections do not change the list printed in Theorem 9.2.7.

## Derived scope and provenance

This is a derived formulation, not a literal transcription. It differs from
the source in the following ways.

- **Corrected axiom list.** `IsValid` uses the ten axioms of corrected
  Definition 4.1.26. Theorem 9.2.7 lists seven of them. The program's
  contract makes the full ten-axiom list its certificate. The source routes
  for 4.1.2, 4.1.8 and 4.1.16 are recorded in the certificate map of the KP
  source ledger (`notes/bruhat-tits/kp-source-ledger.md`, section "Bundle B:
  the complete certificate and its source map").
- **Axiom 4.1.27 omitted.** The unramified descent axiom 4.1.27 (printed
  pp.165–166 / PDF pp.196–197), also asserted by Theorem 9.2.7, is not a
  field of `IsAvailableFor` and is not part of this statement.
- **Existence, not a construction.** The source proves availability for its
  specific construction `B(G_K)^Γ`. The statement asserts only that some
  assignment of data satisfies the axioms, with no reference to unramified
  descent or to the maximal unramified extension.
- **Fields.** KP work over discretely valued fields with Henselian valuation
  ring and perfect residue field. The statement covers nonarchimedean local
  fields of either characteristic in one universe `u`. The cross-field
  comparisons of Axiom 4.1.17 range over such fields only.
- **Comparisons.** Following the published definition, the comparison
  clauses of 4.1.1 and 4.1.17 ask for equivariant building isomorphisms and
  do not formalize their canonicity.

The truth of the statement depends on the published formalization of
corrected Definition 4.1.26 being satisfiable, which is what this target
asks to establish. The published `RootValuationBuildingConstructionStatement`
(proof task `00b6788c-23c3-4b22-88f5-41fdbc6d3654`) is a separate, weaker
target: it asks only for the five Section 4.2 axioms, on parahoric building
data. Published statements that take `𝔅.IsValid` or
`𝔅.IsAvailableFor F G hG` as a hypothesis, such as
`AvailableSimultaneousStandardBasisStatement`, `AvailableCartanStatement`
and `AvailableIwasawaStatement`, are conditional on what this target
asserts.
