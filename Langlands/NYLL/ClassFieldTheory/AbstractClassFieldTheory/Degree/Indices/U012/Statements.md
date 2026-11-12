# NYLL M006.012–014: cardinal relative-index targets

The paired Lean file states three laws for the published cardinal-valued
relative index, under `Langlands.NYLL.ClassFormation`. It adapts Naganori
Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.
The source file SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Source unit and location | Adapted declaration after `Langlands.NYLL.ClassFormation.` | Meaning |
| --- | --- | --- |
| M006.012, lines 143–149, signature 145–147 | `relativeIndexCardinal_eq_index_of_finiteStatement` | For `L ≤ K` and finite `K ⧸ L.subgroupOf K`, the cardinal index equals Mathlib's natural relative index cast to a cardinal. |
| M006.013, lines 151–164, signature 152–153 | `relativeIndexCardinal_selfStatement` | The cardinal relative index of `K` in itself is one. |
| M006.014, lines 166–174, signature 167–170 | `relativeIndexCardinal_mulStatement` | For `M ≤ L ≤ K`, the cardinal indices of the two successive inclusions multiply to that of the composite inclusion. |

All three retain implicit `G : Type u` and `[Group G]`. M006.012
then has implicit `L K : Subgroup G`, explicit `hLK : L ≤ K`,
and the source's implicit instance
`[Finite (K ⧸ L.subgroupOf K)]`, in that order.
M006.013 has explicit `K : Subgroup G`. M006.014 has implicit
`M L K : Subgroup G`, then explicit `hML : M ≤ L` and `hLK : L ≤ K`.
The source's section at lines 23–25 also declares an independent universe
`v`, `D : Type v` and `[Group D]`; these do not occur in any of the
three elaborated declarations and are omitted.

The cardinal in each target is `Cardinal.{u}`. The targets use actual
left-coset cardinality through the existing
`Langlands.NYLL.ClassFormation.relativeIndexCardinal`, imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions`.
That definition and `intersectionIndexCardinal` correspond to source
M006.010–011 at lines 131–141. No normality is required of the
subgroups. Only M006.012 has a finiteness hypothesis: the other two laws
retain infinite coset cardinalities. Mathlib's `Subgroup.relIndex` is
natural-valued and sends infinite indices to zero, so its laws cannot
replace these general cardinal-valued targets.

Worker 120's modifications are extraction of the three signatures,
namespace prefixing, appending `Statement`, turning each theorem's
conclusion into a `def` returning `Prop`, and replacing the original
import by the published data module and `Mathlib.GroupTheory.Index`.
The source's theorem-only `[simp]` attribute on M006.013 is omitted
from this unproved target. The source's unused section variables and
universe are omitted; binder order, visibility and hypotheses are retained.
No instances or proofs are introduced.

A private probe reconstructs source M006.010–014 with the complete
original section telescope and uses the published subgroup-tower
equivalence in the original M006.014 proof. It checks each source
theorem against its full adapted target, the entire cardinal-data
constants against their source definitions, and the exact proposition
bodies by `rfl`. The focused target module compiles and each target
is inspected as returning `Prop` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. This smaller import set
does not need M006.001–009 or the quotient-tower construction to state
the laws. The quotient-tower construction may be used in the separate
M006.014 proof.

These three targets are unproved. They supply neither the later
image–kernel laws nor any local reciprocity or host class-formation
theorem.

The original copyright, Apache-2.0 release and author header are retained.
The retained files are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
