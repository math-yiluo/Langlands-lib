# NYLL M144.015: Membership in a chosen uniformizer-power submodule is scalar-image membership.

`Langlands.NYLL.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff` proves the exact published
`mem_chosenBaseUniformizerPowSubmodule_iffStatement` applied to its original parameters.
The fields share an arbitrary universe `u`, with `[Field K] [Field L] [Algebra K L]`, `[ValuativeRel K]`, `[TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
No finite-dimensional or Galois hypothesis is introduced.

## Implemented proof and dependencies

The proof is `Iff.rfl`, exactly as in the source. Unfolding the statement,
`chosenBaseUniformizerPowSubmodule`, `baseIntegerScalarMulSubmodule` and
`Submodule.map` exposes a witness `y ∈ N` whose image under multiplication
by the chosen uniformizer power is `x`. The linear map evaluates definitionally
to the displayed algebra-map product. The source's `@[simp]` attribute is retained.

The only project import is the published `U015.Statements` module.
All lattice, scalar-image and uniformizer objects used by the target retain
their published definitions. No other new public proof is imported.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 178–186](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L178-L186).
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
