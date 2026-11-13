# NYLL M144 U029: statement targets

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean).
The exact source file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Its registered source is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found under `notes/errata/`.

## Exact source correspondence

The source-line ranges below are the declaration signature and conclusion,
ending immediately before the proof separator. Every original theorem becomes
a `def` returning `Prop`, with the source conclusion as its body. Every explicit,
implicit and instance binder in the source signature stays in the same order;
proof arguments remain parameters even when the conclusion does not refer to them.

| Unit | Original theorem | Source type lines | Adapted proposition definition |
| --- | --- | --- | --- |
| M144.029 | `CyclicCohomology.submodule_pow_succ_mem_of_mul_closed` | 547–551 | `Langlands.NYLL.CyclicCohomology.submodule_pow_succ_mem_of_mul_closedStatement` |
| M144.032 | `CyclicCohomology.inverseCorrectionPartialSum_succ` | 578–580 | `Langlands.NYLL.CyclicCohomology.inverseCorrectionPartialSum_succStatement` |
| M144.033 | `CyclicCohomology.one_add_inverseCorrectionPartialSum_eq_geom_sum` | 586–588 | `Langlands.NYLL.CyclicCohomology.one_add_inverseCorrectionPartialSum_eq_geom_sumStatement` |
| M144.034 | `CyclicCohomology.one_add_mul_one_add_inverseCorrectionPartialSum` | 598–600 | `Langlands.NYLL.CyclicCohomology.one_add_mul_one_add_inverseCorrectionPartialSumStatement` |
| M144.036 | `CyclicCohomology.inverseCorrectionPartialSum_mem_of_mul_closed` | 617–621 | `Langlands.NYLL.CyclicCohomology.inverseCorrectionPartialSum_mem_of_mul_closedStatement` |
| M144.038 | `CyclicCohomology.submodule_isOpen_of_mem_nhds_zero` | 645–648 | `Langlands.NYLL.CyclicCohomology.submodule_isOpen_of_mem_nhds_zeroStatement` |
| M144.039 | `CyclicCohomology.submodule_isClosed_of_isOpen` | 654–657 | `Langlands.NYLL.CyclicCohomology.submodule_isClosed_of_isOpenStatement` |
| M144.040 | `CyclicCohomology.submodule_isClosed_of_mem_nhds_zero` | 663–666 | `Langlands.NYLL.CyclicCohomology.submodule_isClosed_of_mem_nhds_zeroStatement` |
| M144.041 | `CyclicCohomology.submodule_mem_of_tendsto_of_forall_mem_of_closed` | 674–678 | `Langlands.NYLL.CyclicCohomology.submodule_mem_of_tendsto_of_forall_mem_of_closedStatement` |

Finite inverse-correction sums, multiplicative lattice closure and topological submodule properties.

## Mathematical scope and parameter binding

All source fields use the single arbitrary universe `u`. The original section
starts with `(K L : Type u) [Field K] [Field L] [Algebra K L]`
`[FiniteDimensional K L] [IsGalois K L]`, then `[ValuativeRel K]`,
then `[TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
The corresponding source `omit` clauses are retained in the Lean file, except
M144.054 drops its redundant omission of the valuation-extension instances:
those instances are never introduced in this earlier, standalone module. Unused
section parameters do not occur in the resulting definitions. Normal-basis targets
retain finite-dimensional Galois hypotheses; generic submodule targets need none.
The source targets involving only the finite sum need only the extension field.
Valuation-extension targets additionally use `[ValuativeRel L]` and the supplied
`Valuation.HasExtension` instance, and local-field targets on `L` keep their
explicit topology and local-field instance binders. No field, topology, valuation,
uniformizer, lattice or Galois action is replaced with abstract supplied data.


The topology targets use actual neighborhoods, open and closed sets, and convergence of natural-indexed sequences. The finite-sum identities retain their exact truncation indices and signs. No completeness, convergence, inverse-closure or algebraic identity proof is supplied here.


## Reuse, modifications and attribution

Worker 231 extracted these theorem types on 13 November 2026, added the
`Langlands.NYLL` namespace prefix and `Statement` suffix, changed each theorem
to a Prop-valued `def`, and removed every source proof and theorem attribute.
The body is the unchanged source proposition with names resolved to their
namespaced data definitions. The original NYLL imports are replaced by the
minimal data imports displayed in the Lean file; unrelated imported theorems
are unnecessary for the statement layer. Unused namespace-opening commands
are omitted. The unused-variable linter is disabled locally so that original
hypothesis binder names can be preserved even though the proof has been removed.
No source implementation or compatibility patch from a private
port is reused, and no new theorem, axiom, global instance or notation is added.
The supporting data modules reuse Mathlib's actual objects by Lean name.
These proposition definitions provide proof targets only; no theorem proof
is claimed, and they discharge no host class-formation, cup, transfer, Tate
or reciprocity statement.

The original copyright and author header is retained verbatim. Apache-2.0
attribution is retained in the Library's `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
