# NYLL M144.042: `integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension`

This proves exactly
`Langlands.NYLL.CyclicCohomology.integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtensionStatement`
from `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements`.
The theorem uses the required source-adapted name and preserves the target’s
parameters and hypotheses. The published statement and its imports are unchanged.

## Source and attribution

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 687–704](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean#L687-L704).
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
`Langlands.NYLL` namespace prefix, reduced the imports to the published statement and maximal-ideal proof
modules, and wrapped the conclusion in the published proposition definition.
The proof unfolds that definition before following the route below.

## Implemented proof and dependencies

The published `chosenIntegerRingUniformizer_maximalIdeal_eq K` identifies the
base maximal ideal with the span of its chosen uniformizer. Membership in that
span puts the uniformizer in the base maximal ideal. Mathlib's
`Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff` transfers this
membership to the extension valuation ring. This follows the original proof
with only the published proposition wrapper unfolded first.

The direct imports are the published target module and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U006.Proofs`.
The latter supplies the base maximal-ideal equality. The field extension is an
actual `Algebra K L` with compatible valuations. Only K needs the local-field
hypotheses; L needs no topology, local-field, finite-dimensional or Galois
hypothesis. No new axiom or global instance is introduced. This exact support
result discharges no host class-formation, cup, transfer, Tate or reciprocity
target.
