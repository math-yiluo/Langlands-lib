# Proof of `GroupAxiomsExistenceReductionStatement`

The theorem `Langlands.Geometry.Building.groupAxiomsExistenceReduction` has type
`GroupAxiomsExistenceReductionStatement.{u}` for an arbitrary universe `u`, that is,

```lean
RootValuationBuildingConstructionStatement.{u} →
  RootGroupActionAxiomStatement.{u} →
    IwahoriDecompositionAxiomStatement.{u} →
      IntegralModelAxiomsStatement.{u} →
        GroupAxiomsExistenceStatement.{u}
```

It proves the implication only. The four premises are the antecedents of the
implication; none of them, and no other unproved Library statement, is assumed or
proved here. The module imports only the statement module
`Langlands.Geometry.Building.GroupAxiomsExistenceReductionStatement` and adds no
definitions or auxiliary lemmas.

## Proof

The proof introduces the four premises `hC` (construction), `hR` (Axiom 4.1.8
(2)–(3)), `hI` (Axiom 4.1.16) and `hM` (Axioms 4.1.20 and 4.1.22), then the field
`F` with its four instances, the group scheme `G` with its `IsAffineHom G.X.hom`
instance, and `hG : IsConnectedReductive G`.

1. `hC F G hG` gives `P : ParahoricBuildingData G`, a polysimplicial realization
   `R`, an apartment splitting `T` and the seven predicates
   `P.SatisfiesBuildingAxiom R`, `P.HasBoundedOpenStabilizers`,
   `P.SatisfiesAffineApartmentAxiom T`, `P.HasRootReflections`,
   `P.SatisfiesApartmentAxioms`, `P.HasCompatibleApartmentFacets` and
   `P.HasTitsSystem`. The construction statement fixes the instance
   `IsAffineHom G.X.hom` by `hG.isAffineHom`, the conclusion by its binder; since
   `IsAffineHom` is a proposition, the two agree definitionally and no conversion
   is needed.
2. `hM F G P R T` applied to the seven predicates gives integral models `M`,
   special-fibre quotients `Q`, relative root reflection data `ρ`,
   `M.SatisfiesModelAxioms P` and `Q.SatisfiesMorphismAxioms ρ`.
3. `hR F G P` applied to `P.SatisfiesApartmentAxioms` gives
   `P.HasZeroFixerGenerators` and `P.HasRootZeroFixers`.
4. `hI F G P` applied to `P.SatisfiesApartmentAxioms` gives
   `P.HasIwahoriDecomposition`.

The witness is the datum `⟨P, R, T, M, Q, ρ⟩ : KPBuildingDatum G` (fields `base`,
`realization`, `splitting`, `models`, `quotients`, `rootDatum`). Its
`SatisfiesGroupAxioms` is given field by field:

| Field | Axiom | Proof term |
| --- | --- | --- |
| `building` | 4.1.1 for `G` alone | `P.SatisfiesBuildingAxiom R` from step 1 |
| `boundedSubgroups` | 4.1.2 | `P.HasBoundedOpenStabilizers` from step 1 |
| `affineStructure` | 4.1.4 | `P.SatisfiesAffineApartmentAxiom T` from step 1 |
| `affineRootSystem` | 4.1.6 | `⟨HasRootReflections, SatisfiesApartmentAxioms, HasCompatibleApartmentFacets⟩` from step 1 |
| `rootGroupAction` | 4.1.8 | `KPBuildingDatum.satisfiesRootGroupActionAxiom_iff` (clause (1) holds for all data) applied to step 3 |
| `titsSystem` | 4.1.9 | `P.HasTitsSystem` from step 1 |
| `iwahoriDecomposition` | 4.1.16 | step 4 |
| `bruhatTitsGroupSchemes` | 4.1.20 | `M.SatisfiesModelAxioms P` from step 2 |
| `reductiveQuotients` | 4.1.22 | `Q.SatisfiesMorphismAxioms ρ` from step 2 |

This is the route described in the statement's Markdown.

## Provenance

The proof is an internal assembly of published Library statements and the
published adapter `KPBuildingDatum.satisfiesRootGroupActionAxiom_iff`. Its
mathematical context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Definition 4.1.26 (printed p.165 / PDF p.196), with the axiom list
corrected by the authors' corrections of 1 November 2024 (PDF p.27); the
correspondence of each field with an axiom is recorded in
`Langlands/Geometry/Building/FullValidity/Assignment.lean`.
