# M152.028: Galois stability of the lattice uniformizer submodule

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 496–502 (proof: lines 503–542). The source file SHA-256 is
`affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`.
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroup` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroupStatement` |

For each actual Galois automorphism `τ`, the image of the lattice uniformizer
submodule under the restricted Galois linear equivalence equals that submodule.
The actual constructions are imported by Lean name:
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule`
from `NormalBasis.UniformizerSubmodule` and
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`
from `NormalBasis.LatticeMaps.Definitions`, where both module names have prefix
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.`.
The statement retains the explicit coercion from linear equivalence to linear map.

The complete effective source telescope, from lines 24, 28–29, 62 and 497, is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (τ : Gal(L/K))
```

All explicit and instance binders, their order and the single universe are
preserved. No source `omit` applies to this declaration. The exact theorem
statement becomes the body of a Prop-valued definition, with no stability
hypothesis or replacement submodule. The original proof is omitted. The later
same-module quotient equivalence M152.029 requires a separately published proof
of this target before its retained construction can be ported.

Other modifications are the `Langlands.NYLL` namespace prefix, `Statement`
suffix, extraction into this focused pair, explicit binding of the effective
section context and replacement of umbrella imports by published focused imports.
Unused openings and unrelated commands are omitted. No global instance is
introduced. The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
This unproved target establishes no class-formation or reciprocity theorem.
