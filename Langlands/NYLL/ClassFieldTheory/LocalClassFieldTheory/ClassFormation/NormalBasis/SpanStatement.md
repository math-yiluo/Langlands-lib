# NYLL normal-basis span statement

Worker 197 adapts M152.001 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`,
lines 32–42 (target at lines 32–34; section variables at lines 28–29).
The readable original is in the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.span_normalBasis_eq_chosenNormalBasisIntegerLattice` | `Langlands.NYLL.LocalClassFieldTheory.span_normalBasis_eq_chosenNormalBasisIntegerLatticeStatement` |

The proposition equates the integer-ring span of the range of Mathlib's chosen
normal basis with the actual chosen normal-basis integer lattice. It uses the
published `Langlands.NYLL.CyclicCohomology.chosenNormalBasisIntegerLattice`
from `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions`.
That data definition retains the integer-ring span of the orbit of the chosen
normal-basis generator. The proposition's two sides and equality are exactly the
source target.

The single universe `u` and full source telescope are retained in order:
explicit `(K L : Type u)`, then instances `[Field K] [ValuativeRel K] [Field L]
[Algebra K L] [FiniteDimensional K L] [IsGalois K L]`. These are explicit
binders of the proposition definition so the change from a theorem to a
definition cannot drop ambient instances. The source's later topology variables
are outside this declaration's section.

Modifications are the `Langlands.NYLL` namespace prefix, the `Statement` suffix,
replacement of the theorem and proof by a `Prop`-valued definition of its target,
and extraction into this focused pair. The single focused import supplies the
published lattice and the original Mathlib objects; unused imports, namespace
openings and unrelated source commands are omitted. No proof of the target or
new instance is introduced.

The original copyright and author header are retained. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable. This is a
supporting statement and proves no class-formation or reciprocity theorem.
