# NYLL M010.061: evaluation of the named galois quotient projection

This file proves `Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.extensionQuotientMk_applyStatement`
with the source-adapted theorem `Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.extensionQuotientMk_apply`.

Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, implicit `K : ClosedSubgroup G`, explicit
`L : GaloisSubextension K`, then explicit `k : K.toSubgroup`.
Its type is exactly `extensionQuotientMk_applyStatement L k`:
applying `L.extensionQuotientMulEquiv` to `L.extensionQuotientMk k`
equals `QuotientGroup.mk k` in the quotient
`K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup`.

The proof is `rfl`, following M010.061, lines 518–523 (the next unit
starts at 526). The published quotient comparison is `MulEquiv.refl _`,
and the projection is `QuotientGroup.mk'` for the same relative subgroup.
Unfolding these definitions and the named proposition reduces the equality
to reflexivity. No representative choice or finiteness assumption enters
the proof. Normality is supplied by `L.normal` through the published
`extensionSubgroup_normalInstance`.

The sole direct import is `Fields.GaloisSubextension.Statements`, whose
published definitions provide the quotient, comparison and projection.
The original `CyclicCohomology.extensionSubgroup K L.field L.below` is
already replaced in those definitions by its exact Mathlib body
`L.field.toSubgroup.subgroupOf K.toSubgroup`; this proof preserves that
published adaptation. It uses Mathlib's quotient projection definitions
and reflexivity, with no additional theorem dependency. The original
proof body and telescope are retained. The source's `simp` attribute is
omitted; the theorem is available for explicit application.

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The routing reference is `notes/reuse/nyll-public-port-plan.md`, with M010's
unit rows in `notes/reuse/nyll-public-port/m001-m024.md`.

Worker 188 extracts this focused proof, prefixes its namespace with
`Langlands.NYLL`, narrows the source imports to the published modules
listed above, and states the result using the exact published named target.
The original copyright, Apache-2.0 and author header is retained.
The unchanged attribution files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support theorem supplies no host class-formation, cup, transfer, Tate
or reciprocity result.
