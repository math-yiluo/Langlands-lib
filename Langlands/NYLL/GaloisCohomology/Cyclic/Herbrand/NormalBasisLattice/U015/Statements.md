# NYLL M144 U015: statement targets

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
| M144.015 | `CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff` | 178–182 | `Langlands.NYLL.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iffStatement` |
| M144.017 | `CyclicCohomology.chosenBaseUniformizerPow_mul_mem_mono` | 196–199 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPow_mul_mem_monoStatement` |
| M144.018 | `CyclicCohomology.chosenBaseUniformizerPowSubmodule_antitone` | 211–214 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_antitoneStatement` |
| M144.019 | `CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_le` | 227–230 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_leStatement` |
| M144.021 | `CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_top` | 244–247 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_of_field_span_eq_topStatement` |
| M144.022 | `CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_top` | 297–300 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_of_fg_of_field_span_eq_topStatement` |
| M144.023 | `CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_top` | 358–362 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mul_mem_of_fg_of_field_span_eq_topStatement` |
| M144.025 | `CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top` | 453–459 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_topStatement` |
| M144.026 | `CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top` | 484–490 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_topStatement` |
| M144.027 | `CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self` | 514–520 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_selfStatement` |
| M144.028 | `CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ` | 528–534 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succStatement` |
| M144.054 | `CyclicCohomology.chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le` | 981–985 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_leStatement` |

Chosen uniformizer-power membership, descending filtration, denominator clearing and product-depth bounds.

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

The source targets use the actual base uniformizer, scalar-image construction and normal-basis span imported from their definition modules. In particular finite-generation, full-field-span, natural-number bounds and universal membership hypotheses remain exactly as written in the source. No existence or product bound is proved here.



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
