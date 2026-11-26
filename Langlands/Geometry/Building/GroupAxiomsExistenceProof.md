# Existence of building data satisfying the one-group axioms

`Langlands.Geometry.Building.groupAxiomsExistence` proves
`GroupAxiomsExistenceStatement.{u}` for arbitrary `u`. Every connected
reductive group over a nonarchimedean local field of either characteristic
admits a `KPBuildingDatum` satisfying `SatisfiesGroupAxioms` for corrected
Kaletha–Prasad Definition 4.1.26. [Statement](GroupAxiomsExistenceStatement.md)

## Proof

The Lean term applies `groupAxiomsExistenceReduction` to four theorems.
[Reduction](GroupAxiomsExistenceReduction.md)

- `rootValuationBuildingConstruction` supplies parahoric building data,
  their polysimplicial realization and the apartment splitting, together
  with the seven predicates for the corrected Section 4.2 axioms.
  [Construction](RootValuationBuildingConstructionProof.md)
- `rootGroupActionAxiom` supplies Axiom 4.1.8(2)–(3) for these data. The
  reduction uses `KPBuildingDatum.satisfiesRootGroupActionAxiom_iff`
  to obtain the full Axiom 4.1.8, including the half-apartment fixers of
  part (1). [Root-group action](RootGroupActionAxiomProof.md)
- `iwahoriDecompositionAxiom` supplies the Iwahori factorization of
  Axiom 4.1.16 for the same building data.
  [Iwahori decomposition](IwahoriDecompositionAxiomProof.md)
- `integralModelAxioms` constructs the integral model family, special-fibre
  quotient family and relative root reflection data, with Axioms 4.1.20
  and 4.1.22. [Integral models](IntegralModelAxiomsProof.md)

The reduction packages these witnesses into a single `KPBuildingDatum` and
uses the supplied axiom proofs to construct its `SatisfiesGroupAxioms` witness.
This is the one-group existence conclusion in the local-field formulation of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 9.2.7 and
§9.5, with the axiom list of Definition 4.1.26 as corrected on PDF p. 27 of
the authors' 1 November 2024 corrections.
