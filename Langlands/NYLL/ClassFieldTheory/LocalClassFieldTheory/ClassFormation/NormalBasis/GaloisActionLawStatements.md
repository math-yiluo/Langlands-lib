# M152.025–M152.026: Galois action laws on the integer lattice

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`.
M152.025 has statement lines 442–444 and proof lines 445–446;
M152.026 has statement lines 451–455 and proof lines 456–457.
The source file SHA-256 is
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
| `LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_applyStatement` |
| `LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_applyStatement` |

The targets say that the identity Galois automorphism fixes every lattice element
and that the linear equivalence for `τ * υ` applies `υ` first, then `τ`.
Both use the actual published restricted linear equivalence
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`
from `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions`.
Neither target assumes an action law or replaces the equivalence with abstract data.

The common effective source telescope is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
```

M152.025 then binds `(x : chosenNormalBasisIntegerLattice K L)`.
M152.026 then binds `(τ υ : Gal(L/K))` and
`(x : chosenNormalBasisIntegerLattice K L)`, in that order.
The source declares one universe `u` at line 24 and the common section parameters
at lines 28–29. Its `omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
commands at lines 439 and 448 remove both topology instances from these theorems.
The explicit adapted telescopes preserve that omission, all binder kinds and
binder order, with no topology assumptions added.

Each source theorem becomes a Prop-valued definition with the exact statement
as its body. The source proofs and `@[simp]` attributes are omitted; these
unproved targets are same-module prerequisites of the later action construction
M152.035. The construction must wait for separate published proofs.
Other modifications are the `Langlands.NYLL` namespace prefix, `Statement`
suffix, extraction of the two small related targets into this pair, explicit
binding of their effective section context and the focused published import.
Unused openings and unrelated commands are omitted. No global instance is
introduced. The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
These targets establish no class-formation or reciprocity theorem.
