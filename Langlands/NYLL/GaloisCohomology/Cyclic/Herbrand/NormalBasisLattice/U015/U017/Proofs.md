# NYLL M144.017: Increasing the exponent preserves membership after scalar multiplication.

`Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPow_mul_mem_mono` proves the exact published
`chosenBaseUniformizerPow_mul_mem_monoStatement` applied to its original parameters.
The fields share an arbitrary universe `u`, with `[Field K] [Field L] [Algebra K L]`, `[ValuativeRel K]`, `[TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
No finite-dimensional or Galois hypothesis is introduced.

## Implemented proof and dependencies

Write `n = m + d` using `Nat.exists_eq_add_of_le`. The given member of `M`
can be multiplied by the base integer `chosenIntegerRingUniformizer K ^ d`
using `Submodule.smul_mem`. Expanding `Algebra.smul_def`, `pow_add` and
`map_mul`, and rearranging the commutative product, gives the required
uniformizer power. This is the source proof with the statement unfolded.

The only project import is the published `U015.Statements` module.
All lattice, scalar-image and uniformizer objects used by the target retain
their published definitions. No other new public proof is imported.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 196–207](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L196-L207).
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
