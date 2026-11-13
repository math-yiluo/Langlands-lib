# NYLL M010.016: membership in internal field inertia

The theorem
`Langlands.NYLL.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff`
proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.mem_fieldInertiaWithin_iffStatement`.
For implicit `G : Type u`, `[Group G]` and `[TopologicalSpace G]`, its explicit
parameters are `D : DegreeData G`, `K : ClosedSubgroup G` and
`k : K.toSubgroup`. Its conclusion unfolds to
`k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1`.

## Source and adaptation

This is source unit M010.016, Naganori Yamaguchi's
`ClassFormation.DegreeData.mem_fieldInertiaWithin_iff`, in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
lines 129–131 (docstring line 127; `@[simp]` line 128), at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The readable source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is covered by the registered sources
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The routing follows `notes/reuse/nyll-public-port-plan.md`.

Worker 288 extracts this single theorem, prefixes its namespace with
`Langlands.NYLL`, and expresses its type as the already published Statement
definition applied to the same parameters. The source's universe, parameter
order, noncomputable section, docstring, `@[simp]` attribute and `Iff.rfl`
proof are retained. The focused statement import replaces the source's broad
imports and unused namespace opening.

## Implemented proof and dependencies

The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements`.
Its `Fields.Definitions` dependency supplies `DegreeData`, `restrictedDegree`
and `fieldInertiaWithin` on the actual NYLL degree objects, with Mathlib's
subgroups and homomorphism kernels. The imported data in turn uses the focused
NYLL profinite-integer core and cardinal-index definitions.

The implemented proof is exactly `Iff.rfl`. Unfolding the Statement definition
and `fieldInertiaWithin` makes the left side membership in
`(D.restrictedDegree K).toMonoidHom.ker`, which reduces to
`D.restrictedDegree K k = 1`. The definition of the restricted homomorphism
then reduces its evaluation to `D.degree k.1`. Both sides are thus the same
proposition. No earlier field-membership theorem, restricted-degree evaluation
theorem, surjectivity proof, normality instance or finite-residue hypothesis
is needed by this proof term.

This proves only the stated internal-inertia membership criterion. It supplies
no host class-formation, cup, transfer, Tate or reciprocity result.
The original copyright, Apache-2.0 and author header are preserved in the Lean
file. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged; the Lean module comment and this Markdown record the modifications.
