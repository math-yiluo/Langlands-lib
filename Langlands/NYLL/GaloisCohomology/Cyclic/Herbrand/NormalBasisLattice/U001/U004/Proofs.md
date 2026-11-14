# NYLL M144.004: normal-basis vectors belong to the integer lattice

`Langlands.NYLL.CyclicCohomology.normalBasis_mem_integerLattice` proves the
published `normalBasis_mem_integerLatticeStatement K L σ` for every actual
Galois automorphism `σ`. The fields have a common arbitrary universe, with
`[Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]`
and `[ValuativeRel K]`. No topology or local-field hypothesis is needed.

## Implemented proof and dependencies

After unfolding the statement, Mathlib's `IsGalois.normalBasis_apply`
identifies the basis vector indexed by `σ` with the `σ`-conjugate of the
normal-basis generator. It lies in the defining orbit by `Set.mem_range_self`,
and hence in its integer-ring span by `Submodule.subset_span`.
The only project import is the published U001 statement module; the lattice
is the actual `Submodule.span` defined in U002. No other new proof is used.

## Source correspondence and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 67–72](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L67-L72).
The source file has SHA-256
`0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum is listed in `notes/errata/`.

Worker 516 ported the original proof on 14 November 2026, prefixed the namespace
with `Langlands.NYLL`, replaced the source imports with the published statement
import, and made the theorem type the exact statement application, unfolded
at the start of the proof. The mathematical proof route is unchanged.
The original copyright and author header is preserved verbatim; Apache-2.0
attribution is retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support result discharges no host class-formation, cup, transfer, Tate
or reciprocity target.
