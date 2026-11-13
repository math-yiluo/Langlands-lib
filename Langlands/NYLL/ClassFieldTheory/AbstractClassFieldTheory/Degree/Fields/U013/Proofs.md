# NYLL M010.013: membership in field inertia

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.mem_fieldInertia_iffStatement`
with the theorem
`Langlands.NYLL.ClassFormation.DegreeData.mem_fieldInertia_iff`.
Its parameters are implicit `G : Type u`, `[Group G]`, `[TopologicalSpace G]`,
then explicit `D : DegreeData G`, `K : ClosedSubgroup G` and `g : G`.
The theorem's declared conclusion is exactly the named target applied to
`D K g`, which unfolds to
`g ∈ D.fieldInertia K ↔ g ∈ K ∧ D.degree g = 1`.

## Source and attribution

The proof adapts source unit M010.013 from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
lines 110–114: docstring at 110, `@[simp]` at 111, theorem at 112–113
and proof at 114. The source file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The retained snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 287 isolates this theorem, prefixes its namespace with
`Langlands.NYLL`, replaces the source import list by the single published
`Fields.Statements` module, and states the result through its published
Prop-valued target. The source proof term and docstring are preserved.
The source `@[simp]` attribute is omitted; this module adds no simplifier
registration. The source noncomputable section is unnecessary for this proof
and is omitted.

The original copyright, author and Apache-2.0 header is retained.
The Library's [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE)
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged.

## Implemented proof and dependencies

The entire proof is the source term `Iff.rfl`. Unfolding the target and
`fieldInertia` replaces membership in `K ⊓ D.inertia` by the conjunction
of membership in `K` and membership in `D.inertia`. The latter is, by the
definition of `inertia` as `D.degree.toMonoidHom.ker`, the equation
`D.degree g = 1`. Thus both sides reduce to the same proposition.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements`,
which imports the published initial degree and field definitions. Those
definitions supply the actual continuous degree map, inertia kernel and
closed-subgroup intersection, with Mathlib's kernel and intersection
membership definitions. No other NYLL theorem, extra premise or helper
declaration is used. In particular the proof does not use the surjectivity
field of `DegreeData`.

The published target and its imports are unmodified. This theorem supplies
only the field-inertia membership criterion and discharges no host
class-formation, cup-product, transfer, Tate-cohomology or reciprocity target.
