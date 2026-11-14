# NYLL M144.036: `inverseCorrectionPartialSum_mem_of_mul_closed`

This proves exactly
`Langlands.NYLL.CyclicCohomology.inverseCorrectionPartialSum_mem_of_mul_closedStatement`
from `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.Statements`.
The theorem uses the required source-adapted name and preserves the target’s
parameters and hypotheses. The published statement and its imports are unchanged.

## Source and attribution

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 617–631](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L617-L631).
The retained file is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
it is also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found in `notes/errata/`.

The original copyright and author header is retained. The Apache-2.0 license
and notice are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 640 extracted this focused proof on 14 November 2026, added the
`Langlands.NYLL` namespace prefix, reduced the imports to the published statement
module, and wrapped the conclusion in the published proposition definition.
The proof unfolds that definition before following the route below.

## Implemented proof and dependencies

Use finite-sum closure and prove that each positive power of `-x` belongs to the submodule. Negation closure gives the base case, and the given multiplication closure gives the induction step. The source M144.029 prerequisite is proved locally as `hpowers`; no unpublished sibling is imported or redeclared under its public name.

The sole direct import is the published statement module; its imports provide
the actual finite sum, scalar ring, field and Mathlib results used here. No new
axiom or global instance is introduced. This support result has only its exact
stated conclusion and discharges no host class-formation, cup, transfer, Tate
or reciprocity target.
