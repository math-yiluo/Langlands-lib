# M152.005: uniformizer-power scaling is bijective

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 84–85 (proof: lines 86–107). The source file SHA-256 is
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
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap_bijective` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap_bijectiveStatement` |

The target says that multiplication by the chosen base uniformizer to power `n`
is bijective from the actual normal-basis integer lattice onto its `n`th dilate.
It uses the existing
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap`
from `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions`.
No abstract replacement map or bijectivity hypothesis is introduced.

The effective source telescope, from source lines 24, 28–29, 62 and 84, is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat)
```

The single universe, explicit parameters, instance binders and their order are
preserved. The source theorem is replaced by a Prop-valued definition whose body
is exactly its statement. The source proof is omitted; no proof of the target is
claimed. This target is a same-module prerequisite of M152.006, whose actual
construction requires a separately published proof of this bijectivity.

Modifications are the `Langlands.NYLL` namespace prefix, `Statement` suffix,
extraction into this focused pair, explicit binding of the effective source
section context, and replacement of umbrella imports by the published focused
module named above. Unused openings and unrelated commands are omitted.
No global instance is introduced. The original copyright, author and Apache-2.0
header is retained; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
This target establishes no class-formation or reciprocity theorem.
