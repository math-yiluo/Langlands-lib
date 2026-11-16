# M145.006: chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 141–153. The source file SHA-256 is
`5d4eeb8f1dc2a8efeef90ee3c9d89bb43c048d5057e49f32701cefc8768a05c6`. The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction` |

The actual multiplicative distributive Galois action on a subgroup V of the extension integer units whose carrier is the chosen normal-basis principal-unit set at level n.

The full effective source section telescope has the single universe `u` and is:

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

All remaining declaration binders retain their source order and binder kinds in
the Lean file. The source `@[implicit_reducible]` attribute, local ambient integer-unit action, restriction through `subgroupMulDistribMulActionOfStable`, and complete stability proof are retained verbatim. The latter uses the published theorem `galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet`; its Prop-valued statement is not used as a proof. The definition returns action data and declares no global instance.

Modifications are the `Langlands.NYLL` namespace prefix, extraction into this
focused pair and replacement of umbrella imports by the published focused
imports listed in the Lean file. Unused namespace openings and unrelated source
commands are omitted. No conflicting global instance is introduced.
The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This supporting construction or target establishes no class-formation or
reciprocity theorem. Independent semantic acceptance and publication remain
separate from compilation.
