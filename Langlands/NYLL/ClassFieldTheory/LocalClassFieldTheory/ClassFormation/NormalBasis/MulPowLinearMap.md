# M152.004: chosenNormalBasisIntegerLatticeMulPowLinearMap

Worker 197 adapts the source construction from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 66–81. The source file SHA-256 is `affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap` |

For each natural number n, the actual base-integer-ring linear map from the normal-basis integer lattice to its chosen uniformizer-power dilate, multiplying field elements by the image of the chosen base uniformizer raised to n.

This unit is discharged by the existing published declaration with the adapted
name in `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions`.
The paired Lean file imports that module and introduces no second definition
or named alias. This follows Required result 3 of Task 5874.

The existing definition has exactly the pinned source's three fields: `toFun`
multiplies by `algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n)` and
uses the actual published `mem_chosenBaseUniformizerPowSubmodule_iff` proof
with witness `x`; `map_add'` uses `mul_add`; `map_smul'` uses the source
commutative-algebra simplification. The single universe `u`, explicit `K L`,
ordered field, valuation, algebra, finite-dimensional and Galois instances,
base topology and local-field instances, and explicit natural `n` are retained.
The anonymous example checks that complete telescope and exact result type.

The source correspondence and complete construction are also documented in the
published pair `Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis/LatticeMaps/Definitions.lean`
and its same-stem Markdown. Namespace prefixing in that existing port is the
only change to the mathematical names. This compatibility module omits the
already published construction and instead supplies the anonymous type check
shown in Lean; its parameters preserve the source binder order and kinds.
No theorem target is used in place of a required proof.

The correction replaces the earlier extraction that repeated the same fully
qualified declaration. It adds no mathematical claim beyond reuse of the
existing data and its source-telescope check. It establishes no host
class-formation or reciprocity theorem. Independent semantic review and
publication remain separate from compilation.

The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

The focused project Lean check on 16 November 2026, using environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled the anonymous source-telescope
example and inspected the reused definition successfully, with no errors or
warnings.
