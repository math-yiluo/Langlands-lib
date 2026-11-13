# NYLL M144 U042: statement targets

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
| M144.042 | `CyclicCohomology.integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension` | 687–689 | `Langlands.NYLL.CyclicCohomology.integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtensionStatement` |
| M144.043 | `CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension` | 705–708 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtensionStatement` |
| M144.046 | `CyclicCohomology.mem_integerRingFieldSubmodule_iff` | 817–818 | `Langlands.NYLL.CyclicCohomology.mem_integerRingFieldSubmodule_iffStatement` |
| M144.048 | `CyclicCohomology.chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero` | 830–833 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zeroStatement` |
| M144.050 | `CyclicCohomology.mem_maximalIdealFieldSubmodule_iff` | 892–894 | `Langlands.NYLL.CyclicCohomology.mem_maximalIdealFieldSubmodule_iffStatement` |
| M144.052 | `CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fg` | 914–918 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fgStatement` |
| M144.053 | `CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule` | 970–974 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmoduleStatement` |
| M144.055 | `CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule` | 998–1003 | `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmoduleStatement` |
| M144.056 | `CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fg` | 1035–1039 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fgStatement` |
| M144.057 | `CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmodule` | 1048–1053 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmoduleStatement` |
| M144.058 | `CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed` | 1059–1070 | `Langlands.NYLL.CyclicCohomology.exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closedStatement` |

Valuation-extension denominator bounds and integral/maximal-ideal comparisons for normal-basis lattices.

## Mathematical scope and parameter binding

All fields use the single arbitrary universe `u`. The source section starts with
`(K L : Type u) [Field K] [Field L] [Algebra K L]`,
`[FiniteDimensional K L] [IsGalois K L]`, `[ValuativeRel K]`,
`[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, then
`[ValuativeRel L]` and
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
The corresponding source `omit` clauses are retained. Normal-basis targets retain
the finite-dimensional Galois hypotheses; the generic submodule targets omit them.
The two membership characterizations also omit the base topology and local-field
instances, exactly as the source directs. Targets requiring local-field structure
on L retain their original explicit topology and local-field instance binders.

For M144.043 the complete effective source section telescope is written explicitly
before the original topology, local-field and element binders on L. Lean includes
the dependent `HasExtension` section instance in the source theorem even though
its conclusion does not mention that instance. A Prop-valued definition would
otherwise omit it. The materialized telescope preserves the original order and
binder kinds; `FiniteDimensional` and `IsGalois` remain omitted as directed by the
source. No hypothesis is added or removed.

The integer and maximal-ideal submodules are the actual embedded valuation-ring
objects from `U044.Definitions`. The chosen base uniformizer, its scalar action
and the normal-basis orbit span are the actual imported objects. Explicit proof
parameters, including finite generation and the containment bound, remain in
source order even where unused by the proposition body. The final target keeps
the source quantifier order: one threshold, every greater depth, maximal-ideal
containment and multiplicative closure at that depth. No field, topology,
valuation, uniformizer, lattice or Galois action is replaced by supplied data.

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
