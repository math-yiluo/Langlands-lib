# NYLL M144 U009: definitions

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean).
The exact readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its file SHA-256 is `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the original snapshot registration is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence and meaning

| Unit | Original declaration | Source declaration lines | Adapted declaration |
| --- | --- | --- | --- |
| M144.009 | `CyclicCohomology.baseIntegerScalarMulLinearMap` | 127–135 | `Langlands.NYLL.CyclicCohomology.baseIntegerScalarMulLinearMap` |
| M144.011 | `CyclicCohomology.baseIntegerScalarMulSubmodule` | 145–148 | `Langlands.NYLL.CyclicCohomology.baseIntegerScalarMulSubmodule` |

The linear endomorphism given by multiplication by a base integer-ring element, and the actual image of an input submodule under that endomorphism. Both structure-law proof terms in the linear map are unchanged.

## Parameters and modifications

The source's single universe `u`, section parameters and binder kinds are retained.
The source section begins with explicit `(K L : Type u)`, instances
`[Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]`,
then `[ValuativeRel K]`, and, where applicable, `[TopologicalSpace K]`
`[IsNonarchimedeanLocalField K]`. Lean omits section variables unused by a
definition, just as it does in the original. In particular the scalar maps
need no finite-dimensional or Galois hypotheses, and the finite sum needs only
its field `L`. No extra hypothesis is added to compensate for an omitted proof.

Worker 231 extracted the listed source data on 13 November 2026, retained
its construction and all internal proof terms verbatim, added the
`Langlands.NYLL` namespace prefix, and replaced the original NYLL imports
with the imports displayed in the Lean file, omitting an unused namespace-opening command. These imports reuse Mathlib's
actual fields, integer rings, local-field structures and normal basis, plus
already defined NYLL data where named. No original-namespace aliases,
instances, private helpers or theorem proofs are introduced. No compatibility
patch from the feasibility drafts is reused.

The source copyright and author header is retained verbatim. This work is
Apache-2.0; the original `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in the Library. These are support definitions and discharge no host
class-formation, cup, transfer, Tate or reciprocity statement.
