# NYLL uniformizer submodule of the normal-basis integer lattice

Worker 197 adapts M152.008 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 128–132 (section variables at lines 28–29 and 60–62).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule` |

The actual submodule is the comap of the first chosen uniformizer-power
dilate of the chosen normal-basis integer lattice along the lattice's
subtype linear map into the field. Its ambient type is the lattice itself.
Both the type and body are unchanged from the original; in particular this is
data for that particular submodule rather than a proposition asserting the
existence of a submodule.

The single universe `u` and source section variables are retained in order:
explicit `(K L : Type u)`, instances `[Field K] [ValuativeRel K] [Field L]
[Algebra K L] [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`. They give the same effective data telescope.
No valuation or topology on `L`, containment witness or new instance is added.

The focused imports reuse the published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice` from
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions`
and `Langlands.NYLL.CyclicCohomology.chosenBaseUniformizerPowSubmodule` from
the corresponding `U014.Definitions` module. The latter retains multiplication
by the power of the source's chosen base uniformizer.

Modifications are the `Langlands.NYLL` namespace prefix, extraction into this
focused pair, reduction to these published dependency imports, and omission
of unrelated source commands and unused namespace openings. The original data
construction is retained. The copyright and author header is retained; the
Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable.
This supporting definition proves no class-formation or reciprocity theorem.
