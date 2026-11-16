# M152.015: chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFunStatement

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 246–250. The source file SHA-256 is
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`. The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFun` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFunStatement` |

The image of the chosen normal-basis lattice uniformizer submodule under the actual integral lattice basis coordinate map equals the coordinate submodule with every value in the base maximal ideal.

The full effective source section telescope has the single universe `u` and is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
```

All remaining declaration binders retain their source order and binder kinds in
the Lean file. The exact theorem statement becomes a Prop-valued definition with the Statement suffix. The original single universe and all section parameters and instances are bound explicitly in source order, including both base topology and local-field instances. The source proof (lines 251–300) is omitted. The actual published lattice basis, uniformizer submodule and coordinate maximal submodule are reused by Lean name; no equality proof is assumed or supplied.

Modifications are the `Langlands.NYLL` namespace prefix, extraction into this
focused pair and replacement of umbrella imports by the published focused
imports listed in the Lean file. Unused namespace openings and unrelated source
commands are omitted. No conflicting global instance is introduced.
The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This supporting construction or target establishes no class-formation or
reciprocity theorem. Independent semantic acceptance and publication remain
separate from compilation.
