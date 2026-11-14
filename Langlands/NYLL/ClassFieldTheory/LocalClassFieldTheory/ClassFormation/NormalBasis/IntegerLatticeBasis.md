# M152.002: chosenNormalBasisIntegerLatticeBasis

Worker 197 adapts the source construction from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 47–51. The source file SHA-256 is `affcdff9e5fbcb3d65597021d86119933d65af6b842d10a8780bb57f6e6ca684`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis` |

The actual basis of the chosen normal-basis integer lattice, indexed by Gal(L/K) and with coefficients in the base integer ring. It restricts scalars on Mathlib’s chosen normal basis and transports along the published equality of the two spans.

The full effective source telescope is explicit `(K L : Type u)` followed by `[Field K] [ValuativeRel K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]`, in that order. This definition precedes the source’s GradedCoordinates section and has no topology or local-field assumption.

The body is unchanged: `((IsGalois.normalBasis K L).restrictScalars 𝒪[K]).map (LinearEquiv.ofEq _ _ (span_normalBasis_eq_chosenNormalBasisIntegerLattice K L))`. In particular the equality is an actual published proof, not the proposition definition with a Statement suffix.

`Langlands.NYLL.LocalClassFieldTheory.span_normalBasis_eq_chosenNormalBasisIntegerLattice`, imported from `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.U001.Proofs`, supplies the equality proof. The actual lattice is `Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice` from the published `NormalBasisLattice.U002.Definitions` module.

Modifications are the `Langlands.NYLL` namespace prefix, extraction into this
focused pair and replacement of the original umbrella imports by the published
focused imports listed in the Lean file. Unused namespace openings and unrelated
source commands are omitted. The data construction and its proof terms are
preserved; no theorem target is substituted for a proof, and no global instance
is introduced. The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This is a supporting construction. It establishes no class-formation or
reciprocity theorem.
