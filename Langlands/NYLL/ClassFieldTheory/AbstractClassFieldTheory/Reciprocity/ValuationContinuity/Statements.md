# NYLL M301.003, .004 and .009: kernel, closedness and surjectivity targets

Worker 114 adapts Naganori Yamaguchi’s `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean>)
(file SHA-256
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`,
inventory module M301). The source is registered as
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
All three source theorems lie in the source context of lines 22–36
(`noncomputable section`, `namespace ClassFormation`, `universe u`,
`section DegreeOnly`, `variable {G : Type u} [Group G] [TopologicalSpace G]`,
`namespace DegreeData`).

## Source correspondence

Adapted names have prefix `Langlands.NYLL.ClassFormation.DegreeData.`;
original names have prefix `ClassFormation.DegreeData.`.

| Unit | Source lines | Original theorem | Adapted Prop-valued target |
| --- | --- | --- | --- |
| M301.003 | 50–55 | `unramifiedDegreeKernelWithin_eq_ker` | `unramifiedDegreeKernelWithin_eq_kerStatement` |
| M301.004 | 57–70 | `unramifiedDegreeKernelWithin_isClosed` | `unramifiedDegreeKernelWithin_isClosedStatement` |
| M301.009 | 128–141 | `unramifiedDegreeHom_surjective` | `unramifiedDegreeHom_surjectiveStatement` |

Each target keeps the complete source telescope: implicit `{G : Type u}`
(arbitrary universe `u`), `[Group G]`, `[TopologicalSpace G]`, then explicit
`(D : DegreeData G)`, `(K : FiniteResidueAbstractField D)`, `(f : ℕ)` and
`(hf : 0 < f)`, in this order. None requires `IsTopologicalGroup G`.
The propositions are the source theorem types verbatim:

- `unramifiedDegreeKernelWithin_eq_kerStatement D K f hf` is
  `unramifiedDegreeKernelWithin D K f hf =
  (unramifiedDegreeHom D K f hf).toMonoidHom.ker`, an equality of subgroups
  of `K.toSubgroup`.
- `unramifiedDegreeKernelWithin_isClosedStatement D K f hf` is
  `IsClosed (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup)`,
  closedness in the subspace topology of the field subgroup.
- `unramifiedDegreeHom_surjectiveStatement D K f hf` is
  `Function.Surjective (unramifiedDegreeHom D K f hf)`, i.e. every residue
  class in `Multiplicative (ZMod f)` is the reduction modulo `f` of the
  normalized degree `d_K(k)` of some `k` in the field subgroup.

The objects `unramifiedDegreeHom` and `unramifiedDegreeKernelWithin` are the
M301.001–.002 definitions of the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Definitions`
(see its paired Markdown; submitted by the same task as definition
candidate `5edf8a64-061d-463e-b7cf-c2ec7d8e6cbd`), imported here by Lean
name. No other module is imported.

## Modifications

All modifications are by Worker 114.

- The namespace `ClassFormation` is prefixed with `Langlands.NYLL`.
- Each source `theorem` is converted to a `def ...Statement ... : Prop`
  whose body is the source theorem type; the source proofs (`rfl`; preimage
  of `{1}` under a continuous map; surjectivity of `zHatReduction` and of
  `normalizedDegree`) are omitted and will be supplied by separate proof
  tasks. Docstrings are kept.
- The unused source openings `open scoped Topology` and
  `open ClassFormation CyclicCohomology KummerTheory` are omitted.
- The source imports are replaced by the focused Definitions module.
- The intervening M301.005–.008 commands, which need `IsTopologicalGroup G`,
  and all later commands are outside this unit.

No instance, attribute or `simp` lemma is introduced, and these targets
assert nothing beyond the three propositions above.

## License

The original copyright and author header is retained verbatim. The port
remains under Apache-2.0; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, already published in the Library and unchanged.
