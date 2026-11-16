# M150.007: chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`,
lines 230–240. The source file SHA-256 is
`2712c4da08b98e9fbdb071e3c57281fc5e33d3f5fcf6b44c8e85fda77c8a9fa2`. The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits` |

The actual element of the principal-unit subgroup at level 1 + i obtained from the i-th term of a supplied normal-basis correction sequence and its published lattice-bound membership proof.

The full effective source section telescope has the single universe `u` and is:

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
```

All remaining declaration binders retain their source order and binder kinds in
the Lean file. The source body is retained verbatim: the subtype value is `z i`, and its membership field is the actual published theorem `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound` applied to `hb`, `hbn` and `hz i`. The binders `{b n : Nat}` remain implicit; `hb`, `hbn`, `z`, `hz` and `i` remain explicit. No topology on L or integral-closure instance is added.

Modifications are the `Langlands.NYLL` namespace prefix, extraction into this
focused pair and replacement of umbrella imports by the published focused
imports listed in the Lean file. Unused namespace openings and unrelated source
commands are omitted. No conflicting global instance is introduced.
The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This supporting construction or target establishes no class-formation or
reciprocity theorem. Independent semantic acceptance and publication remain
separate from compilation.
