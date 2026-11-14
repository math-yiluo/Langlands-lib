# NYLL M144.007: The chosen normal-basis integer lattice is Galois stable.

`Langlands.NYLL.CyclicCohomology.galoisGroup_apply_mem_chosenNormalBasisIntegerLattice` proves the exact published
`galoisGroup_apply_mem_chosenNormalBasisIntegerLatticeStatement` applied to its original parameters.
The fields share an arbitrary universe `u`, with `[Field K] [Field L] [Algebra K L]`, `[FiniteDimensional K L] [IsGalois K L]`, `[ValuativeRel K]`.
No topology or local-field hypothesis is introduced.

## Implemented proof and dependencies

The proof uses `Submodule.span_induction` on membership in the orbit span.
On a generator indexed by `σ`, applying `τ` gives the normal-basis vector
indexed by `τ * σ`. The source's use of M144.004 is expanded at this point:
`IsGalois.normalBasis_apply` and `Submodule.subset_span` place that conjugate
in the lattice. Zero and addition are preserved by the automorphism and
submodule operations. For scalar multiplication, `τ.commutes` fixes the image
of each base integer, so `map_mul` and `Algebra.smul_def` reduce the claim to
`Submodule.smul_mem`. This is the source proof with the M144.004 step expanded
locally, requiring no pending proof import or second public declaration.
The expanded step has additional provenance in source lines 67–70.

The only project import is the published `U001.Statements` module.
All lattice, scalar-image and uniformizer objects used by the target retain
their published definitions. No other new public proof is imported.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 91–117](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L91-L117).
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
