# NYLL M144.018: The chosen uniformizer-power submodules form a descending filtration.

`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_antitone` proves the exact published
`chosenBaseUniformizerPowSubmodule_antitoneStatement` applied to its original parameters.
The fields share an arbitrary universe `u`, with `[Field K] [Field L] [Algebra K L]`, `[ValuativeRel K]`, `[TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
No finite-dimensional or Galois hypothesis is introduced.

## Implemented proof and dependencies

Unfold the target and expose the scalar-image witness definitionally with
`change`; this expands source M144.015 locally instead of importing its pending
proof. A member of the depth-`n` submodule is a product `π^n y` with `y ∈ N`.
Write `n = m + d` and choose `π^d y` as the witness at depth `m`.
`Submodule.smul_mem` proves this witness remains in `N`. The identity of its
image follows from `pow_add`, `map_mul` and commutativity. This follows the
source M144.018 proof; the definitional membership expansions correspond to
source lines 178–183. There is no second public membership declaration.

The only project import is the published `U015.Statements` module.
All lattice, scalar-image and uniformizer objects used by the target retain
their published definitions. No other new public proof is imported.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 211–224](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L211-L224).
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
