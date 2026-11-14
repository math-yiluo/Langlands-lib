# NYLL M144.008: The chosen normal-basis integer lattice is finitely generated.

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice_fg` proves the exact published
`chosenNormalBasisIntegerLattice_fgStatement` applied to its original parameters.
The fields share an arbitrary universe `u`, with `[Field K] [Field L] [Algebra K L]`, `[FiniteDimensional K L] [IsGalois K L]`, `[ValuativeRel K]`.
No topology or local-field hypothesis is introduced.

## Implemented proof and dependencies

After unfolding the statement and the lattice definition, the proof is
`Submodule.fg_span (Set.finite_range _)`. Mathlib supplies finiteness of the
Galois automorphism group from the finite-dimensional extension, and a finite
range has a finitely generated span. The source proof is otherwise unchanged.

The only project import is the published `U001.Statements` module.
All lattice, scalar-image and uniformizer objects used by the target retain
their published definitions. No other new public proof is imported.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 120–123](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L120-L123).
The source file has SHA-256
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum is listed in `notes/errata/`.

Worker 516 adapted this proof on 14 November 2026, prefixed the namespace with
`Langlands.NYLL`, replaced source imports with the published statement import,
and made the theorem type the exact statement application. Any local expansion
of a source prerequisite is described above. The original copyright and author
header is preserved verbatim; Apache-2.0 attribution is retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support result discharges
no host class-formation, cup, transfer, Tate or reciprocity target.
